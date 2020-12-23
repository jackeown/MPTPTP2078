%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0713+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OTHB3XuhR3

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 16.65s
% Output     : Refutation 16.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   16 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  195 ( 375 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_10_type,type,(
    sk_A_10: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_27_type,type,(
    sk_B_27: $i )).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ ( A @ B ) )
          = ( k9_relat_1 @ ( A @ ( k1_tarski @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X2083: $i,X2084: $i] :
      ( ( ( k11_relat_1 @ ( X2083 @ X2084 ) )
        = ( k9_relat_1 @ ( X2083 @ ( k1_tarski @ X2084 ) ) ) )
      | ~ ( v1_relat_1 @ X2083 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ A ) ) )
        = ( k9_relat_1 @ ( B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X2303: $i,X2304: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( X2303 @ X2304 ) ) )
        = ( k9_relat_1 @ ( X2303 @ X2304 ) ) )
      | ~ ( v1_relat_1 @ X2303 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ ( k1_tarski @ A ) ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ ( B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) )
         => ( ( k2_relat_1 @ ( k7_relat_1 @ ( B @ ( k1_tarski @ A ) ) ) )
            = ( k1_tarski @ ( k1_funct_1 @ ( B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t168_funct_1])).

thf('2',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ ( sk_B_27 @ ( k1_tarski @ sk_A_10 ) ) ) )
 != ( k1_tarski @ ( k1_funct_1 @ ( sk_B_27 @ sk_A_10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k9_relat_1 @ ( sk_B_27 @ ( k1_tarski @ sk_A_10 ) ) )
     != ( k1_tarski @ ( k1_funct_1 @ ( sk_B_27 @ sk_A_10 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_27 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ( k9_relat_1 @ ( sk_B_27 @ ( k1_tarski @ sk_A_10 ) ) )
 != ( k1_tarski @ ( k1_funct_1 @ ( sk_B_27 @ sk_A_10 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ ( sk_A_10 @ ( k1_relat_1 @ sk_B_27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ ( A @ ( k1_relat_1 @ B ) ) )
       => ( ( k11_relat_1 @ ( B @ A ) )
          = ( k1_tarski @ ( k1_funct_1 @ ( B @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2741: $i,X2742: $i] :
      ( ~ ( r2_hidden @ ( X2741 @ ( k1_relat_1 @ X2742 ) ) )
      | ( ( k11_relat_1 @ ( X2742 @ X2741 ) )
        = ( k1_tarski @ ( k1_funct_1 @ ( X2742 @ X2741 ) ) ) )
      | ~ ( v1_funct_1 @ X2742 )
      | ~ ( v1_relat_1 @ X2742 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B_27 )
    | ~ ( v1_funct_1 @ sk_B_27 )
    | ( ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) )
      = ( k1_tarski @ ( k1_funct_1 @ ( sk_B_27 @ sk_A_10 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) )
    = ( k1_tarski @ ( k1_funct_1 @ ( sk_B_27 @ sk_A_10 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ( k9_relat_1 @ ( sk_B_27 @ ( k1_tarski @ sk_A_10 ) ) )
 != ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) ) ),
    inference(demod,[status(thm)],['5','11'])).

thf('13',plain,
    ( ( ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) )
     != ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) ) )
    | ~ ( v1_relat_1 @ sk_B_27 ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_27 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) )
 != ( k11_relat_1 @ ( sk_B_27 @ sk_A_10 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
