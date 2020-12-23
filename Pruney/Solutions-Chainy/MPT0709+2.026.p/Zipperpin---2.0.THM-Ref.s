%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SIeexqRU29

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:09 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 140 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   19
%              Number of atoms          :  632 (1347 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t170_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t170_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_B ) )
      = ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X22 @ X23 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ( ( k1_relat_1 @ sk_B )
        = ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k9_relat_1 @ X21 @ X19 ) @ ( k9_relat_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
      = ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X33 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v2_funct_1 @ X33 )
      | ~ ( r1_tarski @ X31 @ ( k1_relat_1 @ X33 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X33 @ X31 ) @ ( k9_relat_1 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_B @ X1 ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('54',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ),
    inference('sup-',[status(thm)],['10','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['8','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SIeexqRU29
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:07:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.51/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.67  % Solved by: fo/fo7.sh
% 0.51/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.67  % done 628 iterations in 0.222s
% 0.51/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.67  % SZS output start Refutation
% 0.51/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.67  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.67  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.67  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.67  thf(t164_funct_1, conjecture,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.51/0.67         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.51/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.67    (~( ![A:$i,B:$i]:
% 0.51/0.67        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.51/0.67            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.51/0.67    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.51/0.67  thf('0', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(t146_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ B ) =>
% 0.51/0.67       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.67         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.51/0.67  thf('1', plain,
% 0.51/0.67      (![X27 : $i, X28 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 0.51/0.67          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X27)))
% 0.51/0.67          | ~ (v1_relat_1 @ X28))),
% 0.51/0.67      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.51/0.67  thf('2', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.51/0.67  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('4', plain,
% 0.51/0.67      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.67      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.67  thf(d10_xboole_0, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.67  thf('5', plain,
% 0.51/0.67      (![X0 : $i, X2 : $i]:
% 0.51/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.51/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.67  thf('6', plain,
% 0.51/0.67      ((~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)
% 0.51/0.67        | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.67  thf('7', plain,
% 0.51/0.67      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('8', plain,
% 0.51/0.67      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.51/0.67      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.51/0.67  thf('9', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.51/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.67  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.51/0.67  thf(t169_relat_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ A ) =>
% 0.51/0.67       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.51/0.67  thf('11', plain,
% 0.51/0.67      (![X24 : $i]:
% 0.51/0.67         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 0.51/0.67          | ~ (v1_relat_1 @ X24))),
% 0.51/0.67      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.51/0.67  thf(t170_relat_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ B ) =>
% 0.51/0.67       ( r1_tarski @
% 0.51/0.67         ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ B @ ( k2_relat_1 @ B ) ) ) ))).
% 0.51/0.67  thf('12', plain,
% 0.51/0.67      (![X25 : $i, X26 : $i]:
% 0.51/0.67         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ 
% 0.51/0.67           (k10_relat_1 @ X25 @ (k2_relat_1 @ X25)))
% 0.51/0.67          | ~ (v1_relat_1 @ X25))),
% 0.51/0.67      inference('cnf', [status(esa)], [t170_relat_1])).
% 0.51/0.67  thf('13', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.51/0.67           (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.51/0.67          | ~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.51/0.67  thf('14', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.51/0.67             (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.51/0.67  thf('15', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(t36_xboole_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.67  thf('16', plain,
% 0.51/0.67      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.51/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.67  thf(t1_xboole_1, axiom,
% 0.51/0.67    (![A:$i,B:$i,C:$i]:
% 0.51/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.51/0.67       ( r1_tarski @ A @ C ) ))).
% 0.51/0.67  thf('17', plain,
% 0.51/0.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X10 @ X11)
% 0.51/0.67          | ~ (r1_tarski @ X11 @ X12)
% 0.51/0.67          | (r1_tarski @ X10 @ X12))),
% 0.51/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.51/0.67  thf('18', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.67         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.51/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.51/0.67  thf('19', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup-', [status(thm)], ['15', '18'])).
% 0.51/0.67  thf(t12_xboole_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.67  thf('20', plain,
% 0.51/0.67      (![X8 : $i, X9 : $i]:
% 0.51/0.67         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.51/0.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.67  thf('21', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_B))
% 0.51/0.67           = (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.67  thf(t167_relat_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ B ) =>
% 0.51/0.67       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.51/0.67  thf('22', plain,
% 0.51/0.67      (![X22 : $i, X23 : $i]:
% 0.51/0.67         ((r1_tarski @ (k10_relat_1 @ X22 @ X23) @ (k1_relat_1 @ X22))
% 0.51/0.67          | ~ (v1_relat_1 @ X22))),
% 0.51/0.67      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.51/0.67  thf(t10_xboole_1, axiom,
% 0.51/0.67    (![A:$i,B:$i,C:$i]:
% 0.51/0.67     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.51/0.67  thf('23', plain,
% 0.51/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.51/0.67      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.51/0.67  thf('24', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | (r1_tarski @ (k10_relat_1 @ X0 @ X1) @ 
% 0.51/0.67             (k2_xboole_0 @ X2 @ (k1_relat_1 @ X0))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.51/0.67  thf('25', plain,
% 0.51/0.67      (![X1 : $i]:
% 0.51/0.67         ((r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))
% 0.51/0.67          | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup+', [status(thm)], ['21', '24'])).
% 0.51/0.67  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('27', plain,
% 0.51/0.67      (![X1 : $i]:
% 0.51/0.67         (r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('demod', [status(thm)], ['25', '26'])).
% 0.51/0.67  thf('28', plain,
% 0.51/0.67      (![X0 : $i, X2 : $i]:
% 0.51/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.51/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.67  thf('29', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k10_relat_1 @ sk_B @ X0))
% 0.51/0.67          | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ X0)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.67  thf('30', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | ((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['14', '29'])).
% 0.51/0.67  thf('31', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('32', plain,
% 0.51/0.67      (((k1_relat_1 @ sk_B) = (k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)))),
% 0.51/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.51/0.67  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.67      inference('simplify', [status(thm)], ['9'])).
% 0.51/0.67  thf(t147_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.67       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.51/0.67         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.51/0.67  thf('34', plain,
% 0.51/0.67      (![X29 : $i, X30 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 0.51/0.67          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 0.51/0.67          | ~ (v1_funct_1 @ X30)
% 0.51/0.67          | ~ (v1_relat_1 @ X30))),
% 0.51/0.67      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.51/0.67  thf('35', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (v1_relat_1 @ X0)
% 0.51/0.67          | ~ (v1_funct_1 @ X0)
% 0.51/0.67          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.51/0.67              = (k2_relat_1 @ X0)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.67  thf('36', plain,
% 0.51/0.67      ((((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup+', [status(thm)], ['32', '35'])).
% 0.51/0.67  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('39', plain,
% 0.51/0.67      (((k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)) = (k2_relat_1 @ sk_B))),
% 0.51/0.67      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.51/0.67  thf('40', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(t156_relat_1, axiom,
% 0.51/0.67    (![A:$i,B:$i,C:$i]:
% 0.51/0.67     ( ( v1_relat_1 @ C ) =>
% 0.51/0.67       ( ( r1_tarski @ A @ B ) =>
% 0.51/0.67         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.51/0.67  thf('41', plain,
% 0.51/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X19 @ X20)
% 0.51/0.67          | ~ (v1_relat_1 @ X21)
% 0.51/0.67          | (r1_tarski @ (k9_relat_1 @ X21 @ X19) @ (k9_relat_1 @ X21 @ X20)))),
% 0.51/0.67      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.51/0.67  thf('42', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.51/0.67           (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.51/0.67          | ~ (v1_relat_1 @ X0))),
% 0.51/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.67  thf('43', plain,
% 0.51/0.67      (((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.51/0.67        | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.67      inference('sup+', [status(thm)], ['39', '42'])).
% 0.51/0.67  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('45', plain,
% 0.51/0.67      ((r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.51/0.67      inference('demod', [status(thm)], ['43', '44'])).
% 0.51/0.67  thf('46', plain,
% 0.51/0.67      (![X29 : $i, X30 : $i]:
% 0.51/0.67         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 0.51/0.67          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 0.51/0.67          | ~ (v1_funct_1 @ X30)
% 0.51/0.67          | ~ (v1_relat_1 @ X30))),
% 0.51/0.67      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.51/0.67  thf('47', plain,
% 0.51/0.67      ((~ (v1_relat_1 @ sk_B)
% 0.51/0.67        | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67        | ((k9_relat_1 @ sk_B @ 
% 0.51/0.67            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.67            = (k9_relat_1 @ sk_B @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.67  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('50', plain,
% 0.51/0.67      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.51/0.67         = (k9_relat_1 @ sk_B @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.51/0.67  thf(t157_funct_1, axiom,
% 0.51/0.67    (![A:$i,B:$i,C:$i]:
% 0.51/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.67       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.51/0.67           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.51/0.67         ( r1_tarski @ A @ B ) ) ))).
% 0.51/0.67  thf('51', plain,
% 0.51/0.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.67         ((r1_tarski @ X31 @ X32)
% 0.51/0.67          | ~ (v1_relat_1 @ X33)
% 0.51/0.67          | ~ (v1_funct_1 @ X33)
% 0.51/0.67          | ~ (v2_funct_1 @ X33)
% 0.51/0.67          | ~ (r1_tarski @ X31 @ (k1_relat_1 @ X33))
% 0.51/0.67          | ~ (r1_tarski @ (k9_relat_1 @ X33 @ X31) @ (k9_relat_1 @ X33 @ X32)))),
% 0.51/0.67      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.51/0.67  thf('52', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 0.51/0.67          | ~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ 
% 0.51/0.67               (k1_relat_1 @ sk_B))
% 0.51/0.67          | ~ (v2_funct_1 @ sk_B)
% 0.51/0.67          | ~ (v1_funct_1 @ sk_B)
% 0.51/0.67          | ~ (v1_relat_1 @ sk_B)
% 0.51/0.67          | (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ X0))),
% 0.51/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.51/0.67  thf('53', plain,
% 0.51/0.67      (![X1 : $i]:
% 0.51/0.67         (r1_tarski @ (k10_relat_1 @ sk_B @ X1) @ (k1_relat_1 @ sk_B))),
% 0.51/0.67      inference('demod', [status(thm)], ['25', '26'])).
% 0.51/0.67  thf('54', plain, ((v2_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('57', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (r1_tarski @ (k9_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ X0))
% 0.51/0.67          | (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ X0))),
% 0.51/0.67      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.51/0.67  thf('58', plain,
% 0.51/0.67      ((r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 0.51/0.67      inference('sup-', [status(thm)], ['10', '57'])).
% 0.51/0.67  thf('59', plain, ($false), inference('demod', [status(thm)], ['8', '58'])).
% 0.51/0.67  
% 0.51/0.67  % SZS output end Refutation
% 0.51/0.67  
% 0.51/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
