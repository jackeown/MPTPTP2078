%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.11y18dj1VC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 125 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  501 (1003 expanded)
%              Number of equality atoms :   42 (  74 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X26 @ X23 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( ( k3_xboole_0 @ X13 @ ( k1_tarski @ X12 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12','13','21'])).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('30',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('34',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','20'])).

thf('36',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','20'])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','29','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['22','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['6','42'])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_2 ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','43'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_funct_1 @ sk_D @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.11y18dj1VC
% 0.14/0.36  % Computer   : n015.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:13:08 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 58 iterations in 0.030s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(t65_funct_2, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.23/0.51         ( m1_subset_1 @
% 0.23/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.23/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.23/0.51            ( m1_subset_1 @
% 0.23/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.23/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.23/0.51  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t7_funct_2, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.23/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.23/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X23 @ X24)
% 0.23/0.51          | ((X25) = (k1_xboole_0))
% 0.23/0.51          | ~ (v1_funct_1 @ X26)
% 0.23/0.51          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.23/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.23/0.51          | (r2_hidden @ (k1_funct_1 @ X26 @ X23) @ X25))),
% 0.23/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.23/0.51          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.23/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf('4', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.23/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.23/0.51  thf(t111_relat_1, axiom,
% 0.23/0.51    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X17 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.23/0.51  thf(t90_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.23/0.51         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.23/0.51          | ~ (v1_relat_1 @ X18))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf(l29_zfmisc_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.23/0.51       ( r2_hidden @ B @ A ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X12 : $i, X13 : $i]:
% 0.23/0.51         ((r2_hidden @ X12 @ X13)
% 0.23/0.51          | ((k3_xboole_0 @ X13 @ (k1_tarski @ X12)) != (k1_tarski @ X12)))),
% 0.23/0.51      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.23/0.51            != (k1_tarski @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_relat_1 @ k1_xboole_0) != (k1_tarski @ X0))
% 0.23/0.51          | (r2_hidden @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 0.23/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '10'])).
% 0.23/0.51  thf(t60_relat_1, axiom,
% 0.23/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.51  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('13', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(cc1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( v1_relat_1 @ C ) ))).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.51         ((v1_relat_1 @ X20)
% 0.23/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.51  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.51  thf(t110_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (![X16 : $i]:
% 0.23/0.51         (((k7_relat_1 @ X16 @ k1_xboole_0) = (k1_xboole_0))
% 0.23/0.51          | ~ (v1_relat_1 @ X16))),
% 0.23/0.51      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.23/0.51  thf(dt_k7_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X14) | (v1_relat_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.23/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((v1_relat_1 @ k1_xboole_0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.51  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['11', '12', '13', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (![X17 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.23/0.51          | ~ (v1_relat_1 @ X18))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf(t4_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.23/0.51          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ X1)
% 0.23/0.51          | ~ (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0))
% 0.23/0.51          | ~ (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['23', '26'])).
% 0.23/0.51  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('30', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ X18 @ X19))
% 0.23/0.51            = (k3_xboole_0 @ (k1_relat_1 @ X18) @ X19))
% 0.23/0.51          | ~ (v1_relat_1 @ X18))),
% 0.23/0.51      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0))
% 0.23/0.51            = (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['30', '31'])).
% 0.23/0.51  thf('33', plain,
% 0.23/0.51      (![X17 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.23/0.51  thf('34', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.51  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '20'])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.23/0.51  thf(d7_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.51  thf('38', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.23/0.51  thf('39', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.23/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.23/0.51  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.51      inference('sup-', [status(thm)], ['16', '20'])).
% 0.23/0.51  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.51      inference('demod', [status(thm)], ['27', '28', '29', '39', '40'])).
% 0.23/0.51  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.23/0.51      inference('clc', [status(thm)], ['22', '41'])).
% 0.23/0.51  thf('43', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B)))),
% 0.23/0.51      inference('clc', [status(thm)], ['6', '42'])).
% 0.23/0.51  thf('44', plain,
% 0.23/0.51      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_2) @ (k1_tarski @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '43'])).
% 0.23/0.51  thf(d1_tarski, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.51  thf('45', plain,
% 0.23/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X10 @ X9)
% 0.23/0.51          | ((X10) = (X7))
% 0.23/0.51          | ((X9) != (k1_tarski @ X7)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.51  thf('46', plain,
% 0.23/0.51      (![X7 : $i, X10 : $i]:
% 0.23/0.51         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.23/0.51  thf('47', plain, (((k1_funct_1 @ sk_D @ sk_C_2) = (sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['44', '46'])).
% 0.23/0.51  thf('48', plain, (((k1_funct_1 @ sk_D @ sk_C_2) != (sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('49', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
