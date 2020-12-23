%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oft51NBAV0

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:12 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 161 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   20
%              Number of atoms          :  624 (1526 expanded)
%              Number of equality atoms :   33 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) ) @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X8 )
      | ( r1_xboole_0 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) ) )
      | ( r2_hidden @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ X1 )
        | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ sk_A ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ X0 ) ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X11 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X44: $i] :
      ( ( ( k1_relat_1 @ X44 )
       != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','33'])).

thf('35',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('37',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('38',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','33','37'])).

thf('39',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X47 ) )
      | ( r2_hidden @ X45 @ ( k1_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('51',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X39 @ X40 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('52',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['35','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oft51NBAV0
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 313 iterations in 0.165s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.62  thf(t95_relat_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.62         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i]:
% 0.40/0.62        ( ( v1_relat_1 @ B ) =>
% 0.40/0.62          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.62            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.62        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.62         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.40/0.62       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf(dt_k7_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.40/0.62  thf('3', plain,
% 0.40/0.62      (![X42 : $i, X43 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X42) | (v1_relat_1 @ (k7_relat_1 @ X42 @ X43)))),
% 0.40/0.62      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.62        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('split', [status(esa)], ['4'])).
% 0.40/0.62  thf(t89_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ B ) =>
% 0.40/0.62       ( r1_tarski @
% 0.40/0.62         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X48 : $i, X49 : $i]:
% 0.40/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X48 @ X49)) @ 
% 0.40/0.62           (k1_relat_1 @ X48))
% 0.40/0.62          | ~ (v1_relat_1 @ X48))),
% 0.40/0.62      inference('cnf', [status(esa)], [t89_relat_1])).
% 0.40/0.62  thf(t63_xboole_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.40/0.62       ( r1_xboole_0 @ A @ C ) ))).
% 0.40/0.62  thf('7', plain,
% 0.40/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.62         (~ (r1_tarski @ X6 @ X7)
% 0.40/0.62          | ~ (r1_xboole_0 @ X7 @ X8)
% 0.40/0.62          | (r1_xboole_0 @ X6 @ X8))),
% 0.40/0.62      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X0)
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ X2)
% 0.40/0.62          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A)
% 0.40/0.62           | ~ (v1_relat_1 @ sk_B)))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.62  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      ((![X0 : $i]:
% 0.40/0.62          (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)) @ sk_A))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.40/0.62  thf(t3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf(t86_relat_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ C ) =>
% 0.40/0.62       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.40/0.62         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X45 @ (k1_relat_1 @ (k7_relat_1 @ X47 @ X46)))
% 0.40/0.62          | (r2_hidden @ X45 @ X46)
% 0.40/0.62          | ~ (v1_relat_1 @ X47))),
% 0.40/0.62      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.40/0.62  thf('14', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))) @ 
% 0.40/0.62             X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf('16', plain,
% 0.40/0.62      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X4 @ X2)
% 0.40/0.62          | ~ (r2_hidden @ X4 @ X5)
% 0.40/0.62          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.62  thf('18', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X1)
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.40/0.62          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['14', '17'])).
% 0.40/0.62  thf('19', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ X2 @ X0)
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.40/0.62          | ~ (v1_relat_1 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.62  thf('20', plain,
% 0.40/0.62      ((![X0 : $i, X1 : $i]:
% 0.40/0.62          (~ (v1_relat_1 @ X1)
% 0.40/0.62           | (r1_xboole_0 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ sk_A)) @ 
% 0.40/0.62              (k1_relat_1 @ (k7_relat_1 @ sk_B @ X0)))))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['11', '19'])).
% 0.40/0.62  thf(t66_xboole_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X11 : $i]: (((X11) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X11 @ X11))),
% 0.40/0.62      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.40/0.62  thf('22', plain,
% 0.40/0.62      (((~ (v1_relat_1 @ sk_B)
% 0.40/0.62         | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0))))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.62  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf(t64_relat_1, axiom,
% 0.40/0.62    (![A:$i]:
% 0.40/0.62     ( ( v1_relat_1 @ A ) =>
% 0.40/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X44 : $i]:
% 0.40/0.62         (((k1_relat_1 @ X44) != (k1_xboole_0))
% 0.40/0.62          | ((X44) = (k1_xboole_0))
% 0.40/0.62          | ~ (v1_relat_1 @ X44))),
% 0.40/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.62  thf('26', plain,
% 0.40/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.40/0.62         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.40/0.62         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.40/0.62         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.40/0.62  thf('28', plain,
% 0.40/0.62      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '27'])).
% 0.40/0.62  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('30', plain,
% 0.40/0.62      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.40/0.62         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.62  thf('31', plain,
% 0.40/0.62      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.40/0.62         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.40/0.62      inference('split', [status(esa)], ['0'])).
% 0.40/0.62  thf('32', plain,
% 0.40/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.62         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.40/0.62             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.62  thf('33', plain,
% 0.40/0.62      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.40/0.62       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.40/0.62  thf('34', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['2', '33'])).
% 0.40/0.62  thf('35', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['1', '34'])).
% 0.40/0.62  thf('36', plain,
% 0.40/0.62      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.40/0.62         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.40/0.62      inference('split', [status(esa)], ['4'])).
% 0.40/0.62  thf('37', plain,
% 0.40/0.62      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.40/0.62       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('split', [status(esa)], ['4'])).
% 0.40/0.62  thf('38', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['2', '33', '37'])).
% 0.40/0.62  thf('39', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.40/0.62  thf('40', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf('41', plain,
% 0.40/0.62      (![X2 : $i, X3 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf('42', plain,
% 0.40/0.62      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X45 @ X46)
% 0.40/0.62          | ~ (r2_hidden @ X45 @ (k1_relat_1 @ X47))
% 0.40/0.62          | (r2_hidden @ X45 @ (k1_relat_1 @ (k7_relat_1 @ X47 @ X46)))
% 0.40/0.62          | ~ (v1_relat_1 @ X47))),
% 0.40/0.62      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.40/0.62  thf('43', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.40/0.62          | ~ (v1_relat_1 @ X0)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.40/0.62             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.40/0.62          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 0.40/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.40/0.62  thf('44', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.40/0.62             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.40/0.62          | ~ (v1_relat_1 @ X1)
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['40', '43'])).
% 0.40/0.62  thf('45', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i]:
% 0.40/0.62         (~ (v1_relat_1 @ X1)
% 0.40/0.62          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.40/0.62             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.40/0.62          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.40/0.62      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.62  thf('46', plain,
% 0.40/0.62      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 0.40/0.62         (k1_relat_1 @ k1_xboole_0))
% 0.40/0.62        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.40/0.62        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['39', '45'])).
% 0.40/0.62  thf(t60_relat_1, axiom,
% 0.40/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.62  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.62  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('49', plain,
% 0.40/0.62      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 0.40/0.62        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.62      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.40/0.62  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.40/0.62  thf('50', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.40/0.62      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.40/0.62  thf(t55_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.40/0.62  thf('51', plain,
% 0.40/0.62      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ (k2_tarski @ X39 @ X40) @ X41)
% 0.40/0.62          | ~ (r2_hidden @ X39 @ X41))),
% 0.40/0.62      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.40/0.62  thf('52', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.40/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.62  thf('53', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.40/0.62      inference('clc', [status(thm)], ['49', '52'])).
% 0.40/0.62  thf('54', plain, ($false), inference('demod', [status(thm)], ['35', '53'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
