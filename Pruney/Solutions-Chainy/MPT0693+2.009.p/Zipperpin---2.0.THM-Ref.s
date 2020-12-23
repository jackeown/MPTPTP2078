%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JWtXG1dk5U

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:31 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 100 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 ( 877 expanded)
%              Number of equality atoms :   36 (  56 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k10_relat_1 @ X30 @ X31 )
        = ( k10_relat_1 @ X30 @ ( k3_xboole_0 @ ( k2_relat_1 @ X30 ) @ X31 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k2_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k2_relat_1 @ X35 ) )
      | ( ( k9_relat_1 @ X35 @ ( k10_relat_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X22 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k2_subset_1 @ X21 )
      = X21 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( r1_tarski @ X32 @ ( k10_relat_1 @ X33 @ ( k9_relat_1 @ X33 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k3_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k2_relat_1 @ X35 ) )
      | ( ( k9_relat_1 @ X35 @ ( k10_relat_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X28 @ X29 ) @ ( k9_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t148_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_funct_1])).

thf('33',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
     != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JWtXG1dk5U
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 723 iterations in 0.330s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.59/0.78  thf(t168_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( k10_relat_1 @ B @ A ) =
% 0.59/0.78         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (![X30 : $i, X31 : $i]:
% 0.59/0.78         (((k10_relat_1 @ X30 @ X31)
% 0.59/0.78            = (k10_relat_1 @ X30 @ (k3_xboole_0 @ (k2_relat_1 @ X30) @ X31)))
% 0.59/0.78          | ~ (v1_relat_1 @ X30))),
% 0.59/0.78      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.59/0.78  thf(idempotence_k2_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.78  thf('1', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.59/0.78  thf(t29_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.78         (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ (k2_xboole_0 @ X5 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.59/0.78      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf(t147_funct_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.78       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.59/0.78         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X34 : $i, X35 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X34 @ (k2_relat_1 @ X35))
% 0.59/0.78          | ((k9_relat_1 @ X35 @ (k10_relat_1 @ X35 @ X34)) = (X34))
% 0.59/0.78          | ~ (v1_funct_1 @ X35)
% 0.59/0.78          | ~ (v1_relat_1 @ X35))),
% 0.59/0.78      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ((k9_relat_1 @ X0 @ 
% 0.59/0.78              (k10_relat_1 @ X0 @ (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))
% 0.59/0.78              = (k3_xboole_0 @ (k2_relat_1 @ X0) @ X1)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.59/0.78            = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X1)
% 0.59/0.78          | ~ (v1_funct_1 @ X1)
% 0.59/0.78          | ~ (v1_relat_1 @ X1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['0', '5'])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X1)
% 0.59/0.78          | ~ (v1_relat_1 @ X1)
% 0.59/0.78          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.59/0.78              = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf(dt_k2_subset_1, axiom,
% 0.59/0.78    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (![X22 : $i]: (m1_subset_1 @ (k2_subset_1 @ X22) @ (k1_zfmisc_1 @ X22))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.59/0.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.59/0.78  thf('9', plain, (![X21 : $i]: ((k2_subset_1 @ X21) = (X21))),
% 0.59/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.59/0.78  thf('10', plain, (![X22 : $i]: (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X22))),
% 0.59/0.78      inference('demod', [status(thm)], ['8', '9'])).
% 0.59/0.78  thf(t3_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (![X23 : $i, X24 : $i]:
% 0.59/0.78         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.78  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.78  thf(t146_funct_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.59/0.78         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X32 : $i, X33 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X32 @ (k1_relat_1 @ X33))
% 0.59/0.78          | (r1_tarski @ X32 @ (k10_relat_1 @ X33 @ (k9_relat_1 @ X33 @ X32)))
% 0.59/0.78          | ~ (v1_relat_1 @ X33))),
% 0.59/0.78      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | (r1_tarski @ (k1_relat_1 @ X0) @ 
% 0.59/0.78             (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.78  thf(t28_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X3 : $i, X4 : $i]:
% 0.59/0.78         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k3_xboole_0 @ (k1_relat_1 @ X0) @ 
% 0.59/0.78              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.59/0.78              = (k1_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf(t145_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( k9_relat_1 @ B @ A ) =
% 0.59/0.78         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X26 : $i, X27 : $i]:
% 0.59/0.78         (((k9_relat_1 @ X26 @ X27)
% 0.59/0.78            = (k9_relat_1 @ X26 @ (k3_xboole_0 @ (k1_relat_1 @ X26) @ X27)))
% 0.59/0.78          | ~ (v1_relat_1 @ X26))),
% 0.59/0.78      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k9_relat_1 @ X0 @ 
% 0.59/0.78            (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.59/0.78            = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k9_relat_1 @ X0 @ 
% 0.59/0.78              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.59/0.78              = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['18'])).
% 0.59/0.78  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X34 : $i, X35 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X34 @ (k2_relat_1 @ X35))
% 0.59/0.78          | ((k9_relat_1 @ X35 @ (k10_relat_1 @ X35 @ X34)) = (X34))
% 0.59/0.78          | ~ (v1_funct_1 @ X35)
% 0.59/0.78          | ~ (v1_relat_1 @ X35))),
% 0.59/0.78      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.59/0.78              = (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf(t147_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( r1_tarski @
% 0.59/0.78         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i]:
% 0.59/0.78         ((r1_tarski @ (k9_relat_1 @ X28 @ X29) @ 
% 0.59/0.78           (k9_relat_1 @ X28 @ (k1_relat_1 @ X28)))
% 0.59/0.78          | ~ (v1_relat_1 @ X28))),
% 0.59/0.78      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.59/0.78           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.59/0.78             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['24'])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X3 : $i, X4 : $i]:
% 0.59/0.78         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k3_xboole_0 @ (k2_relat_1 @ X0) @ 
% 0.59/0.78              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X1)
% 0.59/0.78          | ~ (v1_relat_1 @ X1)
% 0.59/0.78          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.59/0.78              = (k3_xboole_0 @ (k2_relat_1 @ X1) @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k9_relat_1 @ X0 @ 
% 0.59/0.78            (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.59/0.78            = (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k9_relat_1 @ X0 @ 
% 0.59/0.78              (k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.59/0.78              = (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['19', '30'])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_funct_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.78  thf(t148_funct_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.78       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.59/0.78         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i]:
% 0.59/0.78        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.78          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.59/0.78            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.59/0.78         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.59/0.78          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.78  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.59/0.78         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.59/0.78      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)
% 0.59/0.78          != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_B)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '37'])).
% 0.59/0.78  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.78  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))
% 0.59/0.78         != (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.59/0.78      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.59/0.78  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
