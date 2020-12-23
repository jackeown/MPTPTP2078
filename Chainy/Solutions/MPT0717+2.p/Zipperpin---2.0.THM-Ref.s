%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0717+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.42BOxBXMeK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 16.45s
% Output     : Refutation 16.45s
% Verified   : 
% Statistics : Number of formulae       :   39 (  49 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 389 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_51_type,type,(
    sk_C_51: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_28_type,type,(
    sk_B_28: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_11_type,type,(
    sk_A_11: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t172_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ ( B @ A ) )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ ( C @ ( k1_relat_1 @ B ) ) )
         => ( r2_hidden @ ( k1_funct_1 @ ( B @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ ( B @ A ) )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( r2_hidden @ ( C @ ( k1_relat_1 @ B ) ) )
           => ( r2_hidden @ ( k1_funct_1 @ ( B @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t172_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ ( sk_B_28 @ sk_C_51 ) @ sk_A_11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_C_51 @ ( k1_relat_1 @ sk_B_28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ ( B @ ( k1_relat_1 @ A ) ) )
           => ( ( C
                = ( k1_funct_1 @ ( A @ B ) ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ ( B @ ( k1_relat_1 @ A ) ) )
           => ( ( C
                = ( k1_funct_1 @ ( A @ B ) ) )
            <=> ( r2_hidden @ ( k4_tarski @ ( B @ C ) @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2644: $i,X2645: $i,X2647: $i] :
      ( ~ ( r2_hidden @ ( X2644 @ ( k1_relat_1 @ X2645 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( X2644 @ X2647 ) @ X2645 ) )
      | ( X2647
       != ( k1_funct_1 @ ( X2645 @ X2644 ) ) )
      | ~ ( v1_funct_1 @ X2645 )
      | ~ ( v1_relat_1 @ X2645 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('3',plain,(
    ! [X2644: $i,X2645: $i] :
      ( ~ ( v1_relat_1 @ X2645 )
      | ~ ( v1_funct_1 @ X2645 )
      | ( r2_hidden @ ( k4_tarski @ ( X2644 @ ( k1_funct_1 @ ( X2645 @ X2644 ) ) ) @ X2645 ) )
      | ~ ( r2_hidden @ ( X2644 @ ( k1_relat_1 @ X2645 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_C_51 @ ( k1_funct_1 @ ( sk_B_28 @ sk_C_51 ) ) ) @ sk_B_28 ) )
    | ~ ( v1_funct_1 @ sk_B_28 )
    | ~ ( v1_relat_1 @ sk_B_28 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B_28 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B_28 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_51 @ ( k1_funct_1 @ ( sk_B_28 @ sk_C_51 ) ) ) @ sk_B_28 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( D @ C ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X2111: $i,X2112: $i,X2113: $i,X2114: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( X2111 @ X2112 ) @ X2113 ) )
      | ( r2_hidden @ ( X2112 @ X2114 ) )
      | ( X2114
       != ( k2_relat_1 @ X2113 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X2111: $i,X2112: $i,X2113: $i] :
      ( ( r2_hidden @ ( X2112 @ ( k2_relat_1 @ X2113 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2111 @ X2112 ) @ X2113 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r2_hidden @ ( k1_funct_1 @ ( sk_B_28 @ sk_C_51 ) @ ( k2_relat_1 @ sk_B_28 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v5_relat_1 @ ( sk_B_28 @ sk_A_11 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_B_28 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B_28 @ sk_A_11 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_28 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_28 @ sk_A_11 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_A_11 ) )
      | ~ ( r2_hidden @ ( X0 @ ( k2_relat_1 @ sk_B_28 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ ( sk_B_28 @ sk_C_51 ) @ sk_A_11 ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
