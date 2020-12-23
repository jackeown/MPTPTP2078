%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PXJJ9jXcjq

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:08 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 179 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  549 (1786 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t47_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( r1_xboole_0 @ D @ C ) )
               => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( r1_xboole_0 @ D @ C ) )
                 => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['13','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['13','18'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ~ ( r1_tarski @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X26 @ ( k3_subset_1 @ X26 @ X25 ) )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ sk_D )
    = ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_D ) )
    = sk_D ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['47','52'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_D )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['31','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_D ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_D ) ),
    inference('sup-',[status(thm)],['26','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['4','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PXJJ9jXcjq
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.80/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/0.99  % Solved by: fo/fo7.sh
% 0.80/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/0.99  % done 920 iterations in 0.511s
% 0.80/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/0.99  % SZS output start Refutation
% 0.80/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/0.99  thf(sk_D_type, type, sk_D: $i).
% 0.80/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.80/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/0.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.80/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.80/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/0.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.80/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/0.99  thf(t47_subset_1, conjecture,
% 0.80/0.99    (![A:$i,B:$i]:
% 0.80/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/0.99       ( ![C:$i]:
% 0.80/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00           ( ![D:$i]:
% 0.80/1.00             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.80/1.00                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i,B:$i]:
% 0.80/1.00        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00          ( ![C:$i]:
% 0.80/1.00            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00              ( ![D:$i]:
% 0.80/1.00                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.80/1.00                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 0.80/1.00  thf('0', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(d5_subset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.80/1.00  thf('2', plain,
% 0.80/1.00      (![X20 : $i, X21 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.80/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.00  thf('3', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ sk_D) = (k4_xboole_0 @ sk_A @ sk_D))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('4', plain, (~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_D))),
% 0.80/1.00      inference('demod', [status(thm)], ['0', '3'])).
% 0.80/1.00  thf('5', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(dt_k3_subset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.80/1.00  thf('6', plain,
% 0.80/1.00      (![X22 : $i, X23 : $i]:
% 0.80/1.00         ((m1_subset_1 @ (k3_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.80/1.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.00  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('9', plain,
% 0.80/1.00      (![X20 : $i, X21 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.80/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.00  thf('10', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('11', plain,
% 0.80/1.00      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['7', '10'])).
% 0.80/1.00  thf('12', plain,
% 0.80/1.00      (![X20 : $i, X21 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.80/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.00  thf('13', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 0.80/1.00         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['11', '12'])).
% 0.80/1.00  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf(involutiveness_k3_subset_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.00       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (![X25 : $i, X26 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 0.80/1.00          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.80/1.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.00  thf('16', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.80/1.00      inference('sup-', [status(thm)], ['14', '15'])).
% 0.80/1.00  thf('17', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.80/1.00      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('18', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.80/1.00      inference('demod', [status(thm)], ['16', '17'])).
% 0.80/1.00  thf('19', plain,
% 0.80/1.00      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.80/1.00      inference('sup+', [status(thm)], ['13', '18'])).
% 0.80/1.00  thf(d3_tarski, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( r1_tarski @ A @ B ) <=>
% 0.80/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.80/1.00  thf('20', plain,
% 0.80/1.00      (![X1 : $i, X3 : $i]:
% 0.80/1.00         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.80/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.80/1.00  thf('21', plain,
% 0.80/1.00      (![X1 : $i, X3 : $i]:
% 0.80/1.00         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.80/1.00      inference('cnf', [status(esa)], [d3_tarski])).
% 0.80/1.00  thf('22', plain,
% 0.80/1.00      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.00  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.80/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.80/1.00  thf(t106_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.80/1.00       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.80/1.00  thf('24', plain,
% 0.80/1.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.80/1.00         ((r1_tarski @ X4 @ X5) | ~ (r1_tarski @ X4 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.80/1.00  thf('25', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.80/1.00      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/1.00  thf('26', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.80/1.00      inference('sup+', [status(thm)], ['19', '25'])).
% 0.80/1.00  thf('27', plain,
% 0.80/1.00      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.80/1.00      inference('sup+', [status(thm)], ['13', '18'])).
% 0.80/1.00  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.80/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.80/1.00  thf('29', plain,
% 0.80/1.00      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.80/1.00         ((r1_xboole_0 @ X4 @ X6)
% 0.80/1.00          | ~ (r1_tarski @ X4 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.80/1.00  thf('30', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.80/1.00      inference('sup-', [status(thm)], ['28', '29'])).
% 0.80/1.00  thf('31', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.80/1.00      inference('sup+', [status(thm)], ['27', '30'])).
% 0.80/1.00  thf('32', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('33', plain,
% 0.80/1.00      (![X22 : $i, X23 : $i]:
% 0.80/1.00         ((m1_subset_1 @ (k3_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.80/1.00          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.80/1.00      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.80/1.00  thf('34', plain,
% 0.80/1.00      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.80/1.00  thf('35', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ sk_D) = (k4_xboole_0 @ sk_A @ sk_D))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('36', plain,
% 0.80/1.00      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['34', '35'])).
% 0.80/1.00  thf('37', plain,
% 0.80/1.00      (![X20 : $i, X21 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.80/1.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.80/1.00      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.00  thf('38', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D))
% 0.80/1.00         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['36', '37'])).
% 0.80/1.00  thf('39', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('40', plain,
% 0.80/1.00      (![X25 : $i, X26 : $i]:
% 0.80/1.00         (((k3_subset_1 @ X26 @ (k3_subset_1 @ X26 @ X25)) = (X25))
% 0.80/1.00          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.80/1.00      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.00  thf('41', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_D)) = (sk_D))),
% 0.80/1.00      inference('sup-', [status(thm)], ['39', '40'])).
% 0.80/1.00  thf('42', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ sk_D) = (k4_xboole_0 @ sk_A @ sk_D))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('43', plain,
% 0.80/1.00      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)) = (sk_D))),
% 0.80/1.00      inference('demod', [status(thm)], ['41', '42'])).
% 0.80/1.00  thf('44', plain,
% 0.80/1.00      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_D)) = (sk_D))),
% 0.80/1.00      inference('sup+', [status(thm)], ['38', '43'])).
% 0.80/1.00  thf('45', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 0.80/1.00      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/1.00  thf('46', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.80/1.00      inference('sup+', [status(thm)], ['44', '45'])).
% 0.80/1.00  thf('47', plain, ((r1_xboole_0 @ sk_D @ sk_C_1)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('48', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.80/1.00      inference('simplify', [status(thm)], ['22'])).
% 0.80/1.00  thf(t64_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.80/1.00         ( r1_xboole_0 @ B @ D ) ) =>
% 0.80/1.00       ( r1_xboole_0 @ A @ C ) ))).
% 0.80/1.00  thf('50', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.80/1.00         ((r1_xboole_0 @ X7 @ X8)
% 0.80/1.00          | ~ (r1_tarski @ X7 @ X9)
% 0.80/1.00          | ~ (r1_tarski @ X8 @ X10)
% 0.80/1.00          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.80/1.00      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.80/1.00  thf('51', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.00         (~ (r1_xboole_0 @ X0 @ X1)
% 0.80/1.00          | ~ (r1_tarski @ X2 @ X1)
% 0.80/1.00          | (r1_xboole_0 @ X0 @ X2))),
% 0.80/1.00      inference('sup-', [status(thm)], ['49', '50'])).
% 0.80/1.00  thf('52', plain,
% 0.80/1.00      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_B) | ~ (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.80/1.00      inference('sup-', [status(thm)], ['48', '51'])).
% 0.80/1.00  thf('53', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.80/1.00      inference('sup-', [status(thm)], ['47', '52'])).
% 0.80/1.00  thf(t86_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.80/1.00       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.80/1.00  thf('54', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.80/1.00         (~ (r1_tarski @ X14 @ X15)
% 0.80/1.00          | ~ (r1_xboole_0 @ X14 @ X16)
% 0.80/1.00          | (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.80/1.00  thf('55', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((r1_tarski @ sk_D @ (k4_xboole_0 @ X0 @ sk_B))
% 0.80/1.00          | ~ (r1_tarski @ sk_D @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['53', '54'])).
% 0.80/1.00  thf('56', plain, ((r1_tarski @ sk_D @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.80/1.00      inference('sup-', [status(thm)], ['46', '55'])).
% 0.80/1.00  thf('57', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.00         (~ (r1_xboole_0 @ X0 @ X1)
% 0.80/1.00          | ~ (r1_tarski @ X2 @ X1)
% 0.80/1.00          | (r1_xboole_0 @ X0 @ X2))),
% 0.80/1.00      inference('sup-', [status(thm)], ['49', '50'])).
% 0.80/1.00  thf('58', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((r1_xboole_0 @ X0 @ sk_D)
% 0.80/1.00          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['56', '57'])).
% 0.80/1.00  thf('59', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.80/1.00      inference('sup-', [status(thm)], ['31', '58'])).
% 0.80/1.00  thf('60', plain,
% 0.80/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.80/1.00         (~ (r1_tarski @ X14 @ X15)
% 0.80/1.00          | ~ (r1_xboole_0 @ X14 @ X16)
% 0.80/1.00          | (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.80/1.00  thf('61', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_D))
% 0.80/1.00          | ~ (r1_tarski @ sk_B @ X0))),
% 0.80/1.00      inference('sup-', [status(thm)], ['59', '60'])).
% 0.80/1.00  thf('62', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_D))),
% 0.80/1.00      inference('sup-', [status(thm)], ['26', '61'])).
% 0.80/1.00  thf('63', plain, ($false), inference('demod', [status(thm)], ['4', '62'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
