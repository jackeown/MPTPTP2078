%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0633+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kXwzWbiy0

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  24 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :  106 ( 130 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t35_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t35_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k6_relat_1 @ X2 ) )
      | ( ( k1_funct_1 @ X3 @ X4 )
        = X4 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X2: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X2 ) @ X4 )
        = X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X2 ) @ X4 )
        = X4 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).


%------------------------------------------------------------------------------
