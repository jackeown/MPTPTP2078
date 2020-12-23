%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ev22XQQMXS

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 151 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  543 (1309 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','20'])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( r1_tarski @ ( k5_relat_1 @ X33 @ X34 ) @ ( k5_relat_1 @ X31 @ X32 ) )
      | ~ ( r1_tarski @ X34 @ X32 )
      | ~ ( r1_tarski @ X33 @ X31 )
      | ~ ( v1_relat_1 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X3 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X3 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['40','41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ev22XQQMXS
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 950 iterations in 0.893s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(sk_C_type, type, sk_C: $i).
% 1.13/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.13/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.13/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.13/1.35  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.13/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.13/1.35  thf('0', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf(t17_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.35  thf('2', plain,
% 1.13/1.35      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.13/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.13/1.35      inference('sup+', [status(thm)], ['1', '2'])).
% 1.13/1.35  thf(t3_subset, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.13/1.35  thf('4', plain,
% 1.13/1.35      (![X26 : $i, X28 : $i]:
% 1.13/1.35         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.13/1.35      inference('cnf', [status(esa)], [t3_subset])).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['3', '4'])).
% 1.13/1.35  thf(cc2_relat_1, axiom,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( v1_relat_1 @ A ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.13/1.35  thf('6', plain,
% 1.13/1.35      (![X29 : $i, X30 : $i]:
% 1.13/1.35         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.13/1.35          | (v1_relat_1 @ X29)
% 1.13/1.35          | ~ (v1_relat_1 @ X30))),
% 1.13/1.35      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.13/1.35  thf('7', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['5', '6'])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('9', plain,
% 1.13/1.35      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.13/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.35  thf(d10_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.13/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.13/1.35  thf('11', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.13/1.35      inference('simplify', [status(thm)], ['10'])).
% 1.13/1.35  thf(t19_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.13/1.35       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.13/1.35         (~ (r1_tarski @ X7 @ X8)
% 1.13/1.35          | ~ (r1_tarski @ X7 @ X9)
% 1.13/1.35          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.13/1.35  thf('13', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['11', '12'])).
% 1.13/1.35  thf('14', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ 
% 1.13/1.35          (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.13/1.35      inference('sup-', [status(thm)], ['9', '13'])).
% 1.13/1.35  thf('15', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('16', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ 
% 1.13/1.35          (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.13/1.35      inference('demod', [status(thm)], ['14', '15'])).
% 1.13/1.35  thf('17', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.13/1.35      inference('sup+', [status(thm)], ['1', '2'])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (![X2 : $i, X4 : $i]:
% 1.13/1.35         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.13/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.13/1.35  thf('19', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.13/1.35          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['17', '18'])).
% 1.13/1.35  thf('20', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X1 @ X0)
% 1.13/1.35           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['16', '19'])).
% 1.13/1.35  thf('21', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X0 @ X1)
% 1.13/1.35           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.35      inference('sup+', [status(thm)], ['8', '20'])).
% 1.13/1.35  thf('22', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.13/1.35      inference('simplify', [status(thm)], ['10'])).
% 1.13/1.35  thf('23', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['5', '6'])).
% 1.13/1.35  thf('24', plain,
% 1.13/1.35      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.13/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.35  thf(t50_relat_1, axiom,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( v1_relat_1 @ A ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( v1_relat_1 @ B ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( v1_relat_1 @ C ) =>
% 1.13/1.35               ( ![D:$i]:
% 1.13/1.35                 ( ( v1_relat_1 @ D ) =>
% 1.13/1.35                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 1.13/1.35                     ( r1_tarski @
% 1.13/1.35                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 1.13/1.35  thf('25', plain,
% 1.13/1.35      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X31)
% 1.13/1.35          | ~ (v1_relat_1 @ X32)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X33 @ X34) @ (k5_relat_1 @ X31 @ X32))
% 1.13/1.35          | ~ (r1_tarski @ X34 @ X32)
% 1.13/1.35          | ~ (r1_tarski @ X33 @ X31)
% 1.13/1.35          | ~ (v1_relat_1 @ X34)
% 1.13/1.35          | ~ (v1_relat_1 @ X33))),
% 1.13/1.35      inference('cnf', [status(esa)], [t50_relat_1])).
% 1.13/1.35  thf('26', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.13/1.35          | ~ (r1_tarski @ X2 @ X3)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.13/1.35             (k5_relat_1 @ X3 @ X0))
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X3))),
% 1.13/1.35      inference('sup-', [status(thm)], ['24', '25'])).
% 1.13/1.35  thf('27', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X3 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.13/1.35             (k5_relat_1 @ X2 @ X1))
% 1.13/1.35          | ~ (r1_tarski @ X3 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X3))),
% 1.13/1.35      inference('sup-', [status(thm)], ['23', '26'])).
% 1.13/1.35  thf('28', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 1.13/1.35             (k5_relat_1 @ X0 @ X1))
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X2))),
% 1.13/1.35      inference('sup-', [status(thm)], ['22', '27'])).
% 1.13/1.35  thf('29', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 1.13/1.35             (k5_relat_1 @ X0 @ X1))
% 1.13/1.35          | ~ (v1_relat_1 @ X0))),
% 1.13/1.35      inference('simplify', [status(thm)], ['28'])).
% 1.13/1.35  thf('30', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.13/1.35           (k5_relat_1 @ X2 @ X1))
% 1.13/1.35          | ~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.13/1.35      inference('sup+', [status(thm)], ['21', '29'])).
% 1.13/1.35  thf('31', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X2)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.13/1.35             (k5_relat_1 @ X2 @ X0)))),
% 1.13/1.35      inference('sup-', [status(thm)], ['7', '30'])).
% 1.13/1.35  thf('32', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.13/1.35           (k5_relat_1 @ X2 @ X0))
% 1.13/1.35          | ~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X0))),
% 1.13/1.35      inference('simplify', [status(thm)], ['31'])).
% 1.13/1.35  thf('33', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.13/1.35           (k5_relat_1 @ X2 @ X0))
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X2))),
% 1.13/1.35      inference('sup+', [status(thm)], ['0', '32'])).
% 1.13/1.35  thf('34', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.13/1.35           (k5_relat_1 @ X2 @ X0))
% 1.13/1.35          | ~ (v1_relat_1 @ X2)
% 1.13/1.35          | ~ (v1_relat_1 @ X0))),
% 1.13/1.35      inference('simplify', [status(thm)], ['31'])).
% 1.13/1.35  thf('35', plain,
% 1.13/1.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.13/1.35         (~ (r1_tarski @ X7 @ X8)
% 1.13/1.35          | ~ (r1_tarski @ X7 @ X9)
% 1.13/1.35          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.13/1.35  thf('36', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.13/1.35             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 1.13/1.35          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 1.13/1.35      inference('sup-', [status(thm)], ['34', '35'])).
% 1.13/1.35  thf('37', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X1)
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.13/1.35             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 1.13/1.35          | ~ (v1_relat_1 @ X1)
% 1.13/1.35          | ~ (v1_relat_1 @ X2))),
% 1.13/1.35      inference('sup-', [status(thm)], ['33', '36'])).
% 1.13/1.35  thf('38', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (~ (v1_relat_1 @ X2)
% 1.13/1.35          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.13/1.35             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 1.13/1.35          | ~ (v1_relat_1 @ X0)
% 1.13/1.35          | ~ (v1_relat_1 @ X1))),
% 1.13/1.35      inference('simplify', [status(thm)], ['37'])).
% 1.13/1.35  thf(t52_relat_1, conjecture,
% 1.13/1.35    (![A:$i]:
% 1.13/1.35     ( ( v1_relat_1 @ A ) =>
% 1.13/1.35       ( ![B:$i]:
% 1.13/1.35         ( ( v1_relat_1 @ B ) =>
% 1.13/1.35           ( ![C:$i]:
% 1.13/1.35             ( ( v1_relat_1 @ C ) =>
% 1.13/1.35               ( r1_tarski @
% 1.13/1.35                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.13/1.35                 ( k3_xboole_0 @
% 1.13/1.35                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i]:
% 1.13/1.35        ( ( v1_relat_1 @ A ) =>
% 1.13/1.35          ( ![B:$i]:
% 1.13/1.35            ( ( v1_relat_1 @ B ) =>
% 1.13/1.35              ( ![C:$i]:
% 1.13/1.35                ( ( v1_relat_1 @ C ) =>
% 1.13/1.35                  ( r1_tarski @
% 1.13/1.35                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.13/1.35                    ( k3_xboole_0 @
% 1.13/1.35                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 1.13/1.35  thf('39', plain,
% 1.13/1.35      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.13/1.35          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.13/1.35           (k5_relat_1 @ sk_A @ sk_C)))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('40', plain,
% 1.13/1.35      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 1.13/1.35      inference('sup-', [status(thm)], ['38', '39'])).
% 1.13/1.35  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('44', plain, ($false),
% 1.13/1.35      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.13/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
