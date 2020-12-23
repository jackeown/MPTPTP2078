%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAcuoGiVK2

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 133 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  403 ( 874 expanded)
%              Number of equality atoms :   32 (  77 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( sk_D @ X28 @ X29 @ X30 ) @ X28 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X28 @ X29 @ X30 ) @ ( sk_D @ X28 @ X29 @ X30 ) ) @ X30 )
      | ( X28
        = ( k9_relat_1 @ X30 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ ( k1_tarski @ X19 ) )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,(
    ! [X19: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X19 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','25'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('27',plain,(
    ! [X38: $i] :
      ( ( v1_relat_1 @ X38 )
      | ( r2_hidden @ ( sk_B_1 @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( ( sk_B_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( v1_relat_1 @ X38 )
      | ( ( sk_B_1 @ X38 )
       != ( k4_tarski @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','24'])).

thf('39',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAcuoGiVK2
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 98 iterations in 0.106s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(t150_relat_1, conjecture,
% 0.37/0.56    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.37/0.56  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d13_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ![B:$i,C:$i]:
% 0.37/0.56         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.37/0.56           ( ![D:$i]:
% 0.37/0.56             ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.56               ( ?[E:$i]:
% 0.37/0.56                 ( ( r2_hidden @ E @ B ) & 
% 0.37/0.56                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_D @ X28 @ X29 @ X30) @ X28)
% 0.37/0.56          | (r2_hidden @ 
% 0.37/0.56             (k4_tarski @ (sk_E @ X28 @ X29 @ X30) @ (sk_D @ X28 @ X29 @ X30)) @ 
% 0.37/0.56             X30)
% 0.37/0.56          | ((X28) = (k9_relat_1 @ X30 @ X29))
% 0.37/0.56          | ~ (v1_relat_1 @ X30))),
% 0.37/0.56      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.37/0.56  thf(t48_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X4 : $i, X5 : $i]:
% 0.37/0.56         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.37/0.56           = (k3_xboole_0 @ X4 @ X5))),
% 0.37/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.56  thf(t4_boole, axiom,
% 0.37/0.56    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_boole])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(t4_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.37/0.56          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf(l27_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ (k1_tarski @ X15) @ X16) | (r2_hidden @ X15 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.56  thf(l3_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.37/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i]:
% 0.37/0.56         ((r1_tarski @ X18 @ (k1_tarski @ X19)) | ((X18) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.37/0.56  thf('9', plain, (![X19 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X19))),
% 0.37/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.56  thf(t63_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.56       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X7 @ X8)
% 0.37/0.56          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.37/0.56          | (r1_xboole_0 @ X7 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.37/0.56          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '11'])).
% 0.37/0.56  thf(d1_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X13 @ X12)
% 0.37/0.56          | ((X13) = (X10))
% 0.37/0.56          | ((X12) != (k1_tarski @ X10)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X10 : $i, X13 : $i]:
% 0.37/0.56         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) | ((X1) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.37/0.56          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (((X2) = (X0)) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['15', '20'])).
% 0.37/0.56  thf('22', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.56  thf('24', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.37/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.56  thf('25', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | ((X1) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '25'])).
% 0.37/0.56  thf(d1_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) <=>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.56              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X38 : $i]: ((v1_relat_1 @ X38) | (r2_hidden @ (sk_B_1 @ X38) @ X38))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.56  thf(t4_subset_1, axiom,
% 0.37/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.56  thf(l3_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X20 @ X21)
% 0.37/0.56          | (r2_hidden @ X20 @ X22)
% 0.37/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.37/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | (r2_hidden @ (sk_B_1 @ k1_xboole_0) @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['27', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X10 : $i, X13 : $i]:
% 0.37/0.56         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v1_relat_1 @ k1_xboole_0) | ((sk_B_1 @ k1_xboole_0) = (X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.37/0.56         ((v1_relat_1 @ X38) | ((sk_B_1 @ X38) != (k4_tarski @ X39 @ X40)))),
% 0.37/0.56      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (((X0) != (k4_tarski @ X2 @ X1))
% 0.37/0.56          | (v1_relat_1 @ k1_xboole_0)
% 0.37/0.56          | (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((X1) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.37/0.56      inference('demod', [status(thm)], ['26', '36'])).
% 0.37/0.56  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '24'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '39'])).
% 0.37/0.56  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
