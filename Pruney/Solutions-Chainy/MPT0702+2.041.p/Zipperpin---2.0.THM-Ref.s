%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sMcTncoMlT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 128 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   24
%              Number of atoms          :  608 (1461 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X13 ) ) @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ X15 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( ( k10_relat_1 @ X8 @ ( k2_relat_1 @ X8 ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X3 @ X4 ) @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['4','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k9_relat_1 @ X7 @ X5 ) @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sMcTncoMlT
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 96 iterations in 0.086s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(t157_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.55           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.55         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.55              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.55            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.21/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t152_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ B ) =>
% 0.21/0.55         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X12)
% 0.21/0.55          | (r1_tarski @ (k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X13)) @ X13)
% 0.21/0.55          | ~ (v1_funct_1 @ X12)
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.21/0.55  thf(t155_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ B ) =>
% 0.21/0.55         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X16)
% 0.21/0.55          | ((k10_relat_1 @ X16 @ X17)
% 0.21/0.55              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 0.21/0.55          | ~ (v1_funct_1 @ X16)
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.55  thf(dt_k2_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.21/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.21/0.55          | ~ (v1_funct_1 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf(t154_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( v2_funct_1 @ B ) =>
% 0.21/0.55         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X14)
% 0.21/0.55          | ((k9_relat_1 @ X14 @ X15)
% 0.21/0.55              = (k10_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 0.21/0.55          | ~ (v1_funct_1 @ X14)
% 0.21/0.55          | ~ (v1_relat_1 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.21/0.55          | ~ (v1_funct_1 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.21/0.55          | ~ (v1_funct_1 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf(t169_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X8 : $i]:
% 0.21/0.55         (((k10_relat_1 @ X8 @ (k2_relat_1 @ X8)) = (k1_relat_1 @ X8))
% 0.21/0.55          | ~ (v1_relat_1 @ X8))),
% 0.21/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X9 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.21/0.55          | ~ (v1_funct_1 @ X9)
% 0.21/0.55          | ~ (v1_relat_1 @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X16)
% 0.21/0.55          | ((k10_relat_1 @ X16 @ X17)
% 0.21/0.55              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 0.21/0.55          | ~ (v1_funct_1 @ X16)
% 0.21/0.55          | ~ (v1_relat_1 @ X16))),
% 0.21/0.55      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.21/0.55  thf(t144_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X3 : $i, X4 : $i]:
% 0.21/0.55         ((r1_tarski @ (k9_relat_1 @ X3 @ X4) @ (k2_relat_1 @ X3))
% 0.21/0.55          | ~ (v1_relat_1 @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k10_relat_1 @ X1 @ X0) @ 
% 0.21/0.55           (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_funct_1 @ X1)
% 0.21/0.55          | ~ (v2_funct_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.21/0.55             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.21/0.55           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v2_funct_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['7', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v2_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.55  thf('16', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t1_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.55       ( r1_tarski @ A @ C ) ))).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r1_tarski @ X0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.55        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.55  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('22', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('23', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.21/0.55  thf(t147_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.55         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 0.21/0.55          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 0.21/0.55          | ~ (v1_funct_1 @ X11)
% 0.21/0.55          | ~ (v1_relat_1 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.21/0.55        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '25'])).
% 0.21/0.55  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55          (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))
% 0.21/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55            (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '29'])).
% 0.21/0.55  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.55         (k10_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)) = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.55          = (sk_A))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '33'])).
% 0.21/0.55  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('36', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.55         = (sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t156_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.55         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.55          | ~ (v1_relat_1 @ X7)
% 0.21/0.55          | (r1_tarski @ (k9_relat_1 @ X7 @ X5) @ (k9_relat_1 @ X7 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.55           (k9_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (((r1_tarski @ sk_A @ 
% 0.21/0.55         (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.21/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['38', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | (r1_tarski @ sk_A @ 
% 0.21/0.55           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '42'])).
% 0.21/0.55  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      ((r1_tarski @ sk_A @ 
% 0.21/0.55        (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '46'])).
% 0.21/0.55  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('50', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r1_tarski @ X0 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X0)
% 0.21/0.55          | ~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) @ 
% 0.21/0.55               X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.55        | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '53'])).
% 0.21/0.55  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('58', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.55      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.21/0.55  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
