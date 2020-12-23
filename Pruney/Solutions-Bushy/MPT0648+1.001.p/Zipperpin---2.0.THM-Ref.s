%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0648+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2XtfKUYNTr

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:15 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   36 (  65 expanded)
%              Number of leaves         :   11 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  223 ( 658 expanded)
%              Number of equality atoms :   30 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t55_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
         => ( ( ( k2_relat_1 @ A )
              = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
            & ( ( k1_relat_1 @ A )
              = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_funct_1])).

thf('0',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ( ( k2_funct_1 @ sk_A )
      = ( k4_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('7',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( k2_funct_1 @ sk_A )
    = ( k4_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('14',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
   <= ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_A )
     != ( k2_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_A )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_A )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('21',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_relat_1 @ sk_A )
 != ( k2_relat_1 @ ( k2_funct_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','21'])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','22'])).


%------------------------------------------------------------------------------
