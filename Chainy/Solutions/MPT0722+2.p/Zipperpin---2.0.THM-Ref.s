%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0722+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ro3n9t5Udq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:59 EST 2020

% Result     : Theorem 18.22s
% Output     : Refutation 18.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 148 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  377 (1579 expanded)
%              Number of equality atoms :   25 (  95 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_12_type,type,(
    sk_A_12: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_29_type,type,(
    sk_B_29: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t177_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ ( B @ ( k1_relat_1 @ A ) ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A @ ( k9_relat_1 @ ( A @ B ) ) ) )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v2_funct_1 @ A )
              & ( r1_tarski @ ( B @ ( k1_relat_1 @ A ) ) ) )
           => ( ( k9_relat_1 @ ( k2_funct_1 @ A @ ( k9_relat_1 @ ( A @ B ) ) ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t177_funct_1])).

thf('0',plain,(
    r1_tarski @ ( sk_B_29 @ ( k1_relat_1 @ sk_A_12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ ( A @ ( k1_relat_1 @ B ) ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ ( B @ ( k9_relat_1 @ ( B @ A ) ) ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X2853: $i,X2854: $i] :
      ( ~ ( r1_tarski @ ( X2853 @ ( k1_relat_1 @ X2854 ) ) )
      | ~ ( v2_funct_1 @ X2854 )
      | ( ( k10_relat_1 @ ( X2854 @ ( k9_relat_1 @ ( X2854 @ X2853 ) ) ) )
        = X2853 )
      | ~ ( v1_funct_1 @ X2854 )
      | ~ ( v1_relat_1 @ X2854 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A_12 )
    | ~ ( v1_funct_1 @ sk_A_12 )
    | ( ( k10_relat_1 @ ( sk_A_12 @ ( k9_relat_1 @ ( sk_A_12 @ sk_B_29 ) ) ) )
      = sk_B_29 )
    | ~ ( v2_funct_1 @ sk_A_12 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k10_relat_1 @ ( sk_A_12 @ ( k9_relat_1 @ ( sk_A_12 @ sk_B_29 ) ) ) )
    = sk_B_29 ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A_12 @ ( k9_relat_1 @ ( sk_A_12 @ sk_B_29 ) ) ) )
 != sk_B_29 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X2668: $i] :
      ( ~ ( v2_funct_1 @ X2668 )
      | ( ( k2_funct_1 @ X2668 )
        = ( k4_relat_1 @ X2668 ) )
      | ~ ( v1_funct_1 @ X2668 )
      | ~ ( v1_relat_1 @ X2668 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_A_12 )
    | ( ( k2_funct_1 @ sk_A_12 )
      = ( k4_relat_1 @ sk_A_12 ) )
    | ~ ( v2_funct_1 @ sk_A_12 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_funct_1 @ sk_A_12 )
    = ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ( k9_relat_1 @ ( k4_relat_1 @ sk_A_12 @ ( k9_relat_1 @ ( sk_A_12 @ sk_B_29 ) ) ) )
 != sk_B_29 ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k2_funct_1 @ sk_A_12 )
    = ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X3006: $i] :
      ( ~ ( v2_funct_1 @ X3006 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3006 ) )
        = X3006 )
      | ~ ( v1_funct_1 @ X3006 )
      | ~ ( v1_relat_1 @ X3006 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('17',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A_12 ) )
      = sk_A_12 )
    | ~ ( v1_relat_1 @ sk_A_12 )
    | ~ ( v1_funct_1 @ sk_A_12 )
    | ~ ( v2_funct_1 @ sk_A_12 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_A_12 ) )
    = sk_A_12 ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ ( B @ A ) )
          = ( k10_relat_1 @ ( k2_funct_1 @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X2823: $i,X2824: $i] :
      ( ~ ( v2_funct_1 @ X2823 )
      | ( ( k9_relat_1 @ ( X2823 @ X2824 ) )
        = ( k10_relat_1 @ ( k2_funct_1 @ X2823 @ X2824 ) ) )
      | ~ ( v1_funct_1 @ X2823 )
      | ~ ( v1_relat_1 @ X2823 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A_12 @ X0 ) )
        = ( k10_relat_1 @ ( sk_A_12 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_A_12 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_A_12 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_A_12 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_funct_1 @ sk_A_12 )
    = ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X2669: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X2669 ) )
      | ~ ( v1_funct_1 @ X2669 )
      | ~ ( v1_relat_1 @ X2669 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_A_12 ) )
    | ~ ( v1_relat_1 @ sk_A_12 )
    | ~ ( v1_funct_1 @ sk_A_12 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k2_funct_1 @ sk_A_12 )
    = ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('31',plain,(
    ! [X2669: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X2669 ) )
      | ~ ( v1_funct_1 @ X2669 )
      | ~ ( v1_relat_1 @ X2669 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_A_12 ) )
    | ~ ( v1_relat_1 @ sk_A_12 )
    | ~ ( v1_funct_1 @ sk_A_12 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_A_12 )
    = ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X2696: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X2696 ) )
      | ~ ( v2_funct_1 @ X2696 )
      | ~ ( v1_funct_1 @ X2696 )
      | ~ ( v1_relat_1 @ X2696 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('38',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_A_12 ) )
    | ~ ( v1_relat_1 @ sk_A_12 )
    | ~ ( v1_funct_1 @ sk_A_12 )
    | ~ ( v2_funct_1 @ sk_A_12 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_A_12 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_A_12 ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k4_relat_1 @ sk_A_12 @ X0 ) )
      = ( k10_relat_1 @ ( sk_A_12 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','29','35','42'])).

thf('44',plain,(
    ( k10_relat_1 @ ( sk_A_12 @ ( k9_relat_1 @ ( sk_A_12 @ sk_B_29 ) ) ) )
 != sk_B_29 ),
    inference(demod,[status(thm)],['14','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','44'])).

%------------------------------------------------------------------------------
