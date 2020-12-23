%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i2ngDcgTqe

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 131 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   19
%              Number of atoms          :  647 (1415 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
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

thf('2',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k10_relat_1 @ X16 @ X17 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X16 ) @ X17 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X10 @ X8 ) @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X2 ) @ X1 ) @ X3 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X2 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X2 ) @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( r1_tarski @ ( k10_relat_1 @ X14 @ ( k9_relat_1 @ X14 @ X15 ) ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['39','52','53','54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i2ngDcgTqe
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:47:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.04/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.04/1.27  % Solved by: fo/fo7.sh
% 1.04/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.27  % done 1142 iterations in 0.802s
% 1.04/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.04/1.27  % SZS output start Refutation
% 1.04/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.04/1.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.04/1.27  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.04/1.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.04/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.04/1.27  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.04/1.27  thf(sk_C_type, type, sk_C: $i).
% 1.04/1.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.04/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.04/1.27  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.04/1.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.04/1.27  thf(t157_funct_1, conjecture,
% 1.04/1.27    (![A:$i,B:$i,C:$i]:
% 1.04/1.27     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.04/1.27       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 1.04/1.27           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 1.04/1.27         ( r1_tarski @ A @ B ) ) ))).
% 1.04/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.27    (~( ![A:$i,B:$i,C:$i]:
% 1.04/1.27        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.04/1.27          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 1.04/1.27              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 1.04/1.27            ( r1_tarski @ A @ B ) ) ) )),
% 1.04/1.27    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 1.04/1.27  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf(t155_funct_1, axiom,
% 1.04/1.27    (![A:$i,B:$i]:
% 1.04/1.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.04/1.27       ( ( v2_funct_1 @ B ) =>
% 1.04/1.27         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.04/1.27  thf('1', plain,
% 1.04/1.27      (![X16 : $i, X17 : $i]:
% 1.04/1.27         (~ (v2_funct_1 @ X16)
% 1.04/1.27          | ((k10_relat_1 @ X16 @ X17)
% 1.04/1.27              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 1.04/1.27          | ~ (v1_funct_1 @ X16)
% 1.04/1.27          | ~ (v1_relat_1 @ X16))),
% 1.04/1.27      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.04/1.27  thf(dt_k2_funct_1, axiom,
% 1.04/1.27    (![A:$i]:
% 1.04/1.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.04/1.27       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.04/1.27         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.04/1.27  thf('2', plain,
% 1.04/1.27      (![X11 : $i]:
% 1.04/1.27         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.04/1.27          | ~ (v1_funct_1 @ X11)
% 1.04/1.27          | ~ (v1_relat_1 @ X11))),
% 1.04/1.27      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.04/1.27  thf(t152_funct_1, axiom,
% 1.04/1.27    (![A:$i,B:$i]:
% 1.04/1.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.04/1.27       ( ( v2_funct_1 @ B ) =>
% 1.04/1.27         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 1.04/1.27  thf('3', plain,
% 1.04/1.27      (![X14 : $i, X15 : $i]:
% 1.04/1.27         (~ (v2_funct_1 @ X14)
% 1.04/1.27          | (r1_tarski @ (k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X15)) @ X15)
% 1.04/1.27          | ~ (v1_funct_1 @ X14)
% 1.04/1.27          | ~ (v1_relat_1 @ X14))),
% 1.04/1.27      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.04/1.27  thf('4', plain,
% 1.04/1.27      (![X11 : $i]:
% 1.04/1.27         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.04/1.27          | ~ (v1_funct_1 @ X11)
% 1.04/1.27          | ~ (v1_relat_1 @ X11))),
% 1.04/1.27      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.04/1.27  thf(d10_xboole_0, axiom,
% 1.04/1.27    (![A:$i,B:$i]:
% 1.04/1.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.04/1.27  thf('5', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.04/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.04/1.27  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.04/1.27      inference('simplify', [status(thm)], ['5'])).
% 1.04/1.27  thf(t12_xboole_1, axiom,
% 1.04/1.27    (![A:$i,B:$i]:
% 1.04/1.27     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.04/1.27  thf('7', plain,
% 1.04/1.27      (![X6 : $i, X7 : $i]:
% 1.04/1.27         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.04/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.04/1.27  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.04/1.27      inference('sup-', [status(thm)], ['6', '7'])).
% 1.04/1.27  thf('9', plain,
% 1.04/1.27      (![X16 : $i, X17 : $i]:
% 1.04/1.27         (~ (v2_funct_1 @ X16)
% 1.04/1.27          | ((k10_relat_1 @ X16 @ X17)
% 1.04/1.27              = (k9_relat_1 @ (k2_funct_1 @ X16) @ X17))
% 1.04/1.27          | ~ (v1_funct_1 @ X16)
% 1.04/1.27          | ~ (v1_relat_1 @ X16))),
% 1.04/1.27      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.04/1.27  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.04/1.27      inference('simplify', [status(thm)], ['5'])).
% 1.04/1.27  thf(t11_xboole_1, axiom,
% 1.04/1.27    (![A:$i,B:$i,C:$i]:
% 1.04/1.27     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.04/1.27  thf('11', plain,
% 1.04/1.27      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.27         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.04/1.27      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.04/1.27  thf('12', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 1.04/1.27      inference('sup-', [status(thm)], ['10', '11'])).
% 1.04/1.27  thf(t156_relat_1, axiom,
% 1.04/1.27    (![A:$i,B:$i,C:$i]:
% 1.04/1.27     ( ( v1_relat_1 @ C ) =>
% 1.04/1.27       ( ( r1_tarski @ A @ B ) =>
% 1.04/1.27         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 1.04/1.27  thf('13', plain,
% 1.04/1.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.04/1.27         (~ (r1_tarski @ X8 @ X9)
% 1.04/1.27          | ~ (v1_relat_1 @ X10)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ X10 @ X8) @ (k9_relat_1 @ X10 @ X9)))),
% 1.04/1.27      inference('cnf', [status(esa)], [t156_relat_1])).
% 1.04/1.27  thf('14', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.27         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 1.04/1.27           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.04/1.27          | ~ (v1_relat_1 @ X2))),
% 1.04/1.27      inference('sup-', [status(thm)], ['12', '13'])).
% 1.04/1.27  thf('15', plain,
% 1.04/1.27      (![X6 : $i, X7 : $i]:
% 1.04/1.27         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.04/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.04/1.27  thf('16', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.27         (~ (v1_relat_1 @ X2)
% 1.04/1.27          | ((k2_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ 
% 1.04/1.27              (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 1.04/1.27              = (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.04/1.27      inference('sup-', [status(thm)], ['14', '15'])).
% 1.04/1.27  thf('17', plain,
% 1.04/1.27      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.04/1.27         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 1.04/1.27      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.04/1.27  thf('18', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 1.04/1.27          | ~ (v1_relat_1 @ X2)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 1.04/1.27      inference('sup-', [status(thm)], ['16', '17'])).
% 1.04/1.27  thf('19', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 1.04/1.27          | ~ (v1_relat_1 @ X2)
% 1.04/1.27          | ~ (v1_funct_1 @ X2)
% 1.04/1.27          | ~ (v2_funct_1 @ X2)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ X2) @ X1) @ X3)
% 1.04/1.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X2)))),
% 1.04/1.27      inference('sup-', [status(thm)], ['9', '18'])).
% 1.04/1.27  thf('20', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.04/1.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X2))
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ X2) @ X0) @ X1)
% 1.04/1.27          | ~ (v2_funct_1 @ X2)
% 1.04/1.27          | ~ (v1_funct_1 @ X2)
% 1.04/1.27          | ~ (v1_relat_1 @ X2))),
% 1.04/1.27      inference('sup-', [status(thm)], ['8', '19'])).
% 1.04/1.27  thf('21', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.27         (~ (v1_relat_1 @ X0)
% 1.04/1.27          | ~ (v1_funct_1 @ X0)
% 1.04/1.27          | ~ (v1_relat_1 @ X0)
% 1.04/1.27          | ~ (v1_funct_1 @ X0)
% 1.04/1.27          | ~ (v2_funct_1 @ X0)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ X0) @ X2) @ X1)
% 1.04/1.27          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ X2) @ X1))),
% 1.04/1.27      inference('sup-', [status(thm)], ['4', '20'])).
% 1.04/1.27  thf('22', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k10_relat_1 @ X0 @ X2) @ X1)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ (k2_funct_1 @ X0) @ X2) @ X1)
% 1.04/1.27          | ~ (v2_funct_1 @ X0)
% 1.04/1.27          | ~ (v1_funct_1 @ X0)
% 1.04/1.27          | ~ (v1_relat_1 @ X0))),
% 1.04/1.27      inference('simplify', [status(thm)], ['21'])).
% 1.04/1.27  thf('23', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]:
% 1.04/1.27         (~ (v1_relat_1 @ X1)
% 1.04/1.27          | ~ (v1_funct_1 @ X1)
% 1.04/1.27          | ~ (v2_funct_1 @ X1)
% 1.04/1.27          | ~ (v1_relat_1 @ X1)
% 1.04/1.27          | ~ (v1_funct_1 @ X1)
% 1.04/1.27          | ~ (v2_funct_1 @ X1)
% 1.04/1.27          | (r1_tarski @ 
% 1.04/1.27             (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 1.04/1.27      inference('sup-', [status(thm)], ['3', '22'])).
% 1.04/1.27  thf('24', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]:
% 1.04/1.27         ((r1_tarski @ 
% 1.04/1.27           (k9_relat_1 @ (k2_funct_1 @ X1) @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 1.04/1.27          | ~ (v2_funct_1 @ X1)
% 1.04/1.27          | ~ (v1_funct_1 @ X1)
% 1.04/1.27          | ~ (v1_relat_1 @ X1))),
% 1.04/1.27      inference('simplify', [status(thm)], ['23'])).
% 1.04/1.27  thf('25', plain,
% 1.04/1.27      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('26', plain,
% 1.04/1.27      (![X6 : $i, X7 : $i]:
% 1.04/1.27         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.04/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.04/1.27  thf('27', plain,
% 1.04/1.27      (((k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 1.04/1.27         = (k9_relat_1 @ sk_C @ sk_B))),
% 1.04/1.27      inference('sup-', [status(thm)], ['25', '26'])).
% 1.04/1.27  thf('28', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 1.04/1.27          | ~ (v1_relat_1 @ X2)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ X2 @ X1) @ X3))),
% 1.04/1.27      inference('sup-', [status(thm)], ['16', '17'])).
% 1.04/1.27  thf('29', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]:
% 1.04/1.27         (~ (r1_tarski @ (k9_relat_1 @ X1 @ (k9_relat_1 @ sk_C @ sk_B)) @ X0)
% 1.04/1.27          | (r1_tarski @ (k9_relat_1 @ X1 @ (k9_relat_1 @ sk_C @ sk_A)) @ X0)
% 1.04/1.27          | ~ (v1_relat_1 @ X1))),
% 1.04/1.27      inference('sup-', [status(thm)], ['27', '28'])).
% 1.04/1.27  thf('30', plain,
% 1.04/1.27      ((~ (v1_relat_1 @ sk_C)
% 1.04/1.27        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.27        | ~ (v2_funct_1 @ sk_C)
% 1.04/1.27        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.04/1.27        | (r1_tarski @ 
% 1.04/1.27           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 1.04/1.27           sk_B))),
% 1.04/1.27      inference('sup-', [status(thm)], ['24', '29'])).
% 1.04/1.27  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('34', plain,
% 1.04/1.27      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.04/1.27        | (r1_tarski @ 
% 1.04/1.27           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 1.04/1.27           sk_B))),
% 1.04/1.27      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 1.04/1.27  thf('35', plain,
% 1.04/1.27      ((~ (v1_relat_1 @ sk_C)
% 1.04/1.27        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.27        | (r1_tarski @ 
% 1.04/1.27           (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 1.04/1.27           sk_B))),
% 1.04/1.27      inference('sup-', [status(thm)], ['2', '34'])).
% 1.04/1.27  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('38', plain,
% 1.04/1.27      ((r1_tarski @ 
% 1.04/1.27        (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)),
% 1.04/1.27      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.04/1.27  thf('39', plain,
% 1.04/1.27      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_B)
% 1.04/1.27        | ~ (v1_relat_1 @ sk_C)
% 1.04/1.27        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.27        | ~ (v2_funct_1 @ sk_C))),
% 1.04/1.27      inference('sup+', [status(thm)], ['1', '38'])).
% 1.04/1.27  thf('40', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf(t146_funct_1, axiom,
% 1.04/1.27    (![A:$i,B:$i]:
% 1.04/1.27     ( ( v1_relat_1 @ B ) =>
% 1.04/1.27       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 1.04/1.27         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 1.04/1.27  thf('41', plain,
% 1.04/1.27      (![X12 : $i, X13 : $i]:
% 1.04/1.27         (~ (r1_tarski @ X12 @ (k1_relat_1 @ X13))
% 1.04/1.27          | (r1_tarski @ X12 @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X12)))
% 1.04/1.27          | ~ (v1_relat_1 @ X13))),
% 1.04/1.27      inference('cnf', [status(esa)], [t146_funct_1])).
% 1.04/1.27  thf('42', plain,
% 1.04/1.27      ((~ (v1_relat_1 @ sk_C)
% 1.04/1.27        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 1.04/1.27      inference('sup-', [status(thm)], ['40', '41'])).
% 1.04/1.27  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('44', plain,
% 1.04/1.27      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 1.04/1.27      inference('demod', [status(thm)], ['42', '43'])).
% 1.04/1.27  thf('45', plain,
% 1.04/1.27      (![X14 : $i, X15 : $i]:
% 1.04/1.27         (~ (v2_funct_1 @ X14)
% 1.04/1.27          | (r1_tarski @ (k10_relat_1 @ X14 @ (k9_relat_1 @ X14 @ X15)) @ X15)
% 1.04/1.27          | ~ (v1_funct_1 @ X14)
% 1.04/1.27          | ~ (v1_relat_1 @ X14))),
% 1.04/1.27      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.04/1.27  thf('46', plain,
% 1.04/1.27      (![X0 : $i, X2 : $i]:
% 1.04/1.27         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.04/1.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.04/1.27  thf('47', plain,
% 1.04/1.27      (![X0 : $i, X1 : $i]:
% 1.04/1.27         (~ (v1_relat_1 @ X1)
% 1.04/1.27          | ~ (v1_funct_1 @ X1)
% 1.04/1.27          | ~ (v2_funct_1 @ X1)
% 1.04/1.27          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.04/1.27          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 1.04/1.27      inference('sup-', [status(thm)], ['45', '46'])).
% 1.04/1.27  thf('48', plain,
% 1.04/1.27      ((((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 1.04/1.27        | ~ (v2_funct_1 @ sk_C)
% 1.04/1.27        | ~ (v1_funct_1 @ sk_C)
% 1.04/1.27        | ~ (v1_relat_1 @ sk_C))),
% 1.04/1.27      inference('sup-', [status(thm)], ['44', '47'])).
% 1.04/1.27  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('52', plain,
% 1.04/1.27      (((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 1.04/1.27      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.04/1.27  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('55', plain, ((v2_funct_1 @ sk_C)),
% 1.04/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.27  thf('56', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.04/1.27      inference('demod', [status(thm)], ['39', '52', '53', '54', '55'])).
% 1.04/1.27  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 1.04/1.27  
% 1.04/1.27  % SZS output end Refutation
% 1.04/1.27  
% 1.04/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
