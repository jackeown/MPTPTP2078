%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0618+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2FmggzDV0w

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:58 EST 2020

% Result     : Theorem 15.14s
% Output     : Refutation 15.14s
% Verified   : 
% Statistics : Number of formulae       :   20 (  26 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  113 ( 197 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_16_type,type,(
    sk_B_16: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_7_type,type,(
    sk_A_7: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t12_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) )
       => ( r2_hidden @ ( k1_funct_1 @ ( B @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) )
         => ( r2_hidden @ ( k1_funct_1 @ ( B @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ ( sk_B_16 @ sk_A_7 ) @ ( k2_relat_1 @ sk_B_16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_7 @ ( k1_relat_1 @ sk_B_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ ( A @ D ) ) )
                  & ( r2_hidden @ ( D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X2622: $i,X2624: $i,X2626: $i,X2627: $i] :
      ( ( X2624
       != ( k2_relat_1 @ X2622 ) )
      | ( r2_hidden @ ( X2626 @ X2624 ) )
      | ~ ( r2_hidden @ ( X2627 @ ( k1_relat_1 @ X2622 ) ) )
      | ( X2626
       != ( k1_funct_1 @ ( X2622 @ X2627 ) ) )
      | ~ ( v1_funct_1 @ X2622 )
      | ~ ( v1_relat_1 @ X2622 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X2622: $i,X2627: $i] :
      ( ~ ( v1_relat_1 @ X2622 )
      | ~ ( v1_funct_1 @ X2622 )
      | ~ ( r2_hidden @ ( X2627 @ ( k1_relat_1 @ X2622 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( X2622 @ X2627 ) @ ( k2_relat_1 @ X2622 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( sk_B_16 @ sk_A_7 ) @ ( k2_relat_1 @ sk_B_16 ) ) )
    | ~ ( v1_funct_1 @ sk_B_16 )
    | ~ ( v1_relat_1 @ sk_B_16 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_relat_1 @ sk_B_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ ( k1_funct_1 @ ( sk_B_16 @ sk_A_7 ) @ ( k2_relat_1 @ sk_B_16 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7'])).

%------------------------------------------------------------------------------
