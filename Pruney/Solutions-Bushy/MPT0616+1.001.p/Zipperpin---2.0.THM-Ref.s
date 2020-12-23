%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0616+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j9ewKWuZSg

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  86 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  448 (1070 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t8_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
        <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( B
              = ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( sk_B
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k1_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X3
        = ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C_1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
        | ( X0
          = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_C_1 )
        | ( X0
          = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      & ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ( sk_B
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      & ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('23',plain,
    ( ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X3 ) @ X1 )
      | ( X3
       != ( k1_funct_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
      & ( sk_B
        = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','10','21','22','33'])).


%------------------------------------------------------------------------------
