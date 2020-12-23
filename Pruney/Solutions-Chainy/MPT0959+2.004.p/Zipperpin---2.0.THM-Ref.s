%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p2Hh6IWyR9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 (  99 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  655 ( 872 expanded)
%              Number of equality atoms :   29 (  51 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t32_wellord2,conjecture,(
    ! [A: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ A ) )
      = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_wellord2 @ ( k1_tarski @ A ) )
        = ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_wellord2])).

thf('0',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k4_tarski @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_wellord2 @ X32 ) )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ( r2_hidden @ ( k4_tarski @ X34 @ X35 ) @ X33 )
      | ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('6',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X32 ) )
      | ~ ( r1_tarski @ X34 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ X34 @ X35 ) @ ( k1_wellord2 @ X32 ) )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ~ ( r2_hidden @ X34 @ X32 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('7',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('8',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ X34 @ X35 ) @ ( k1_wellord2 @ X32 ) )
      | ~ ( r2_hidden @ X35 @ X32 )
      | ~ ( r2_hidden @ X34 @ X32 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) )
      | ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('23',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
       != ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('24',plain,(
    ! [X32: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X32 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
        = X32 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('26',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D_1 @ X24 @ X25 ) ) @ X25 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X29 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X32: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X32 ) )
      = X32 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D_1 @ X24 @ X25 ) ) @ X25 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( ( sk_D_1 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X24 @ X25 ) @ ( sk_D_1 @ X24 @ X25 ) ) @ X24 )
      | ( r1_tarski @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X36: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) ) @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_wellord2 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','53'])).

thf('55',plain,(
    ( k1_wellord2 @ ( k1_tarski @ sk_A ) )
 != ( k1_wellord2 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p2Hh6IWyR9
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:26:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 159 iterations in 0.080s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(t32_wellord2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.21/0.53       ( k1_tarski @ ( k4_tarski @ A @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( k1_wellord2 @ ( k1_tarski @ A ) ) =
% 0.21/0.53          ( k1_tarski @ ( k4_tarski @ A @ A ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t32_wellord2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.21/0.53         != (k1_tarski @ (k4_tarski @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d1_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('2', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('4', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(d1_wellord2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.53         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.53           ( ![C:$i,D:$i]:
% 0.21/0.53             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.53               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.53                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         (((X33) != (k1_wellord2 @ X32))
% 0.21/0.53          | ~ (r2_hidden @ X34 @ X32)
% 0.21/0.53          | ~ (r2_hidden @ X35 @ X32)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X34 @ X35) @ X33)
% 0.21/0.53          | ~ (r1_tarski @ X34 @ X35)
% 0.21/0.53          | ~ (v1_relat_1 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ (k1_wellord2 @ X32))
% 0.21/0.53          | ~ (r1_tarski @ X34 @ X35)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X34 @ X35) @ (k1_wellord2 @ X32))
% 0.21/0.53          | ~ (r2_hidden @ X35 @ X32)
% 0.21/0.53          | ~ (r2_hidden @ X34 @ X32))),
% 0.21/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.53  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.53  thf('7', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X34 @ X35)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X34 @ X35) @ (k1_wellord2 @ X32))
% 0.21/0.53          | ~ (r2_hidden @ X35 @ X32)
% 0.21/0.53          | ~ (r2_hidden @ X34 @ X32))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '10'])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.53          | ((X10) = (X7))
% 0.21/0.53          | ((X9) != (k1_tarski @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X7 : $i, X10 : $i]:
% 0.21/0.53         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.53          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k1_tarski @ (k4_tarski @ X0 @ X0)) @ 
% 0.21/0.53          (k1_wellord2 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X4 : $i, X6 : $i]:
% 0.21/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.21/0.53             (k1_tarski @ (k4_tarski @ X0 @ X0)))
% 0.21/0.53          | ((k1_wellord2 @ (k1_tarski @ X0))
% 0.21/0.53              = (k1_tarski @ (k4_tarski @ X0 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i]:
% 0.21/0.53         (((X33) != (k1_wellord2 @ X32))
% 0.21/0.53          | ((k3_relat_1 @ X33) = (X32))
% 0.21/0.53          | ~ (v1_relat_1 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X32 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ (k1_wellord2 @ X32))
% 0.21/0.53          | ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.53  thf('25', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.53  thf('26', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf(d3_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53           ( ![C:$i,D:$i]:
% 0.21/0.53             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.53               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         ((r2_hidden @ 
% 0.21/0.53           (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D_1 @ X24 @ X25)) @ X25)
% 0.21/0.53          | (r1_tarski @ X25 @ X24)
% 0.21/0.53          | ~ (v1_relat_1 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.53  thf(t30_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.53         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.53           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 0.21/0.53          | (r2_hidden @ X29 @ (k3_relat_1 @ X31))
% 0.21/0.53          | ~ (v1_relat_1 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.53          | (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['26', '30'])).
% 0.21/0.53  thf('32', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_C_2 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X7 : $i, X10 : $i]:
% 0.21/0.53         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | ((sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain, (![X32 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X32)) = (X32))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         ((r2_hidden @ 
% 0.21/0.53           (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D_1 @ X24 @ X25)) @ X25)
% 0.21/0.53          | (r1_tarski @ X25 @ X24)
% 0.21/0.53          | ~ (v1_relat_1 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 0.21/0.53          | (r2_hidden @ X30 @ (k3_relat_1 @ X31))
% 0.21/0.53          | ~ (v1_relat_1 @ X31))),
% 0.21/0.53      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D_1 @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.53          | (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['36', '40'])).
% 0.21/0.53  thf('42', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ (sk_D_1 @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X7 : $i, X10 : $i]:
% 0.21/0.53         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | ((sk_D_1 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) = (X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (r2_hidden @ 
% 0.21/0.53             (k4_tarski @ (sk_C_2 @ X24 @ X25) @ (sk_D_1 @ X24 @ X25)) @ X24)
% 0.21/0.53          | (r1_tarski @ X25 @ X24)
% 0.21/0.53          | ~ (v1_relat_1 @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ 
% 0.21/0.53             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.21/0.53             X1)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ (k1_wellord2 @ (k1_tarski @ X0)))
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain, (![X36 : $i]: (v1_relat_1 @ (k1_wellord2 @ X36))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ 
% 0.21/0.53             (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ X0) @ 
% 0.21/0.53             X1)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.21/0.53      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | ~ (r2_hidden @ 
% 0.21/0.53               (k4_tarski @ (sk_C_2 @ X1 @ (k1_wellord2 @ (k1_tarski @ X0))) @ 
% 0.21/0.53                X0) @ 
% 0.21/0.53               X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ X1)
% 0.21/0.53          | ~ (r2_hidden @ (k4_tarski @ X0 @ X0) @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k1_wellord2 @ (k1_tarski @ X0)) @ 
% 0.21/0.53          (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k1_wellord2 @ (k1_tarski @ X0))
% 0.21/0.53           = (k1_tarski @ (k4_tarski @ X0 @ X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((k1_wellord2 @ (k1_tarski @ sk_A))
% 0.21/0.53         != (k1_wellord2 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['0', '54'])).
% 0.21/0.53  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
