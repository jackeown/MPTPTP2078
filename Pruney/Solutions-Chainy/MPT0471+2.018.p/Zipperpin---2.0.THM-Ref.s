%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uKDhfknC6P

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 (  88 expanded)
%              Number of leaves         :   36 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  590 ( 636 expanded)
%              Number of equality atoms :   77 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X28 @ X29 ) @ ( k4_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf(t61_setfam_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t61_setfam_1])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X22 @ X23 ) @ X22 )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t61_setfam_1])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X22 @ X23 ) @ X23 )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( sk_C_1 @ ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i] :
      ( ( ( k3_relat_1 @ X27 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X27 ) @ ( k2_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('17',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','22'])).

thf('24',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','23'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_tarski @ X21 )
       != ( k2_xboole_0 @ X19 @ X20 ) )
      | ( zip_tseitin_2 @ X20 @ X19 @ X21 )
      | ( zip_tseitin_1 @ X20 @ X19 @ X21 )
      | ( zip_tseitin_0 @ X20 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
       != X0 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X2 )
      | ( zip_tseitin_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X2 )
      | ( zip_tseitin_2 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( zip_tseitin_2 @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X2 ) @ X2 )
      | ( zip_tseitin_1 @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X2 ) @ X2 )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) @ ( k1_tarski @ X2 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X18
        = ( k1_tarski @ X16 ) )
      | ~ ( zip_tseitin_2 @ X18 @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) @ X0 )
      | ( zip_tseitin_1 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_tarski @ X15 ) )
      | ~ ( zip_tseitin_1 @ X14 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t18_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X8 ) )
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X8 ) )
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( X0 = X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uKDhfknC6P
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:11:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 57 iterations in 0.030s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(t63_relat_1, conjecture,
% 0.22/0.50    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.22/0.50  thf('0', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(fc7_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( v1_relat_1 @
% 0.22/0.50       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.50         (v1_relat_1 @ 
% 0.22/0.50          (k2_tarski @ (k4_tarski @ X28 @ X29) @ (k4_tarski @ X30 @ X31)))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.22/0.50  thf(t61_setfam_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( m1_subset_1 @
% 0.22/0.50       ( k1_tarski @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X24 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t61_setfam_1])).
% 0.22/0.50  thf(t10_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50            ( ![C:$i]:
% 0.22/0.50              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         ((r2_hidden @ (sk_C_1 @ X22 @ X23) @ X22)
% 0.22/0.50          | ((X22) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.22/0.50             (k1_tarski @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X3 : $i, X6 : $i]:
% 0.22/0.50         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | ((sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))
% 0.22/0.50              = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X24 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k1_tarski @ k1_xboole_0) @ 
% 0.22/0.50          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t61_setfam_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (sk_C_1 @ X22 @ X23) @ X23)
% 0.22/0.50          | ((X22) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | (m1_subset_1 @ 
% 0.22/0.50             (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0)) @ 
% 0.22/0.50             (k1_zfmisc_1 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf(cc2_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X25 : $i, X26 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.22/0.50          | (v1_relat_1 @ X25)
% 0.22/0.50          | ~ (v1_relat_1 @ X26))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | (v1_relat_1 @ 
% 0.22/0.50             (sk_C_1 @ (k1_tarski @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_relat_1 @ k1_xboole_0)
% 0.22/0.50          | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['7', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X0)
% 0.22/0.50          | ((k1_tarski @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50          | (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('15', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(d6_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k3_relat_1 @ A ) =
% 0.22/0.50         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X27 : $i]:
% 0.22/0.50         (((k3_relat_1 @ X27)
% 0.22/0.50            = (k2_xboole_0 @ (k1_relat_1 @ X27) @ (k2_relat_1 @ X27)))
% 0.22/0.50          | ~ (v1_relat_1 @ X27))),
% 0.22/0.50      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((((k3_relat_1 @ k1_xboole_0)
% 0.22/0.50          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.22/0.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(t1_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.50  thf('21', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k1_tarski @ k1_xboole_0) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.50      inference('clc', [status(thm)], ['14', '22'])).
% 0.22/0.50  thf('24', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '23'])).
% 0.22/0.50  thf(t22_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)) = (X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.22/0.50  thf(t43_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.50          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.22/0.50          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_4, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_6, axiom,
% 0.22/0.50    (![C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.22/0.50       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_7, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.50          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (((k1_tarski @ X21) != (k2_xboole_0 @ X19 @ X20))
% 0.22/0.50          | (zip_tseitin_2 @ X20 @ X19 @ X21)
% 0.22/0.50          | (zip_tseitin_1 @ X20 @ X19 @ X21)
% 0.22/0.50          | (zip_tseitin_0 @ X20 @ X19 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (((k1_tarski @ X2) != (X0))
% 0.22/0.50          | (zip_tseitin_0 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X2)
% 0.22/0.50          | (zip_tseitin_1 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X2)
% 0.22/0.50          | (zip_tseitin_2 @ (k3_xboole_0 @ X0 @ X1) @ X0 @ X2))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]:
% 0.22/0.50         ((zip_tseitin_2 @ (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 0.22/0.50           (k1_tarski @ X2) @ X2)
% 0.22/0.50          | (zip_tseitin_1 @ (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 0.22/0.50             (k1_tarski @ X2) @ X2)
% 0.22/0.50          | (zip_tseitin_0 @ (k3_xboole_0 @ (k1_tarski @ X2) @ X1) @ 
% 0.22/0.50             (k1_tarski @ X2) @ X2))),
% 0.22/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.50         (((X18) = (k1_tarski @ X16)) | ~ (zip_tseitin_2 @ X18 @ X17 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 0.22/0.50           (k1_tarski @ X0) @ X0)
% 0.22/0.50          | (zip_tseitin_1 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 0.22/0.50             (k1_tarski @ X0) @ X0)
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (((X14) = (k1_tarski @ X15)) | ~ (zip_tseitin_1 @ X14 @ X13 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.50          | (zip_tseitin_0 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1) @ 
% 0.22/0.50             (k1_tarski @ X0) @ X0))),
% 0.22/0.50      inference('clc', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (((X12) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X12 @ X11 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf(t18_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.50         ( k1_tarski @ A ) ) =>
% 0.22/0.50       ( ( A ) = ( B ) ) ))).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (((X9) = (X8))
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X8))
% 0.22/0.50              != (k1_tarski @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.22/0.50              = (k1_xboole_0))
% 0.22/0.50          | ((X0) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X0) = (X1))
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.22/0.50              = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         (((X9) = (X8))
% 0.22/0.50          | ((k3_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X8))
% 0.22/0.50              != (k1_tarski @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_xboole_0) != (k1_tarski @ X0)) | ((X0) = (X1)) | ((X0) = (X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((X0) = (X1)) | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((k1_xboole_0) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '40'])).
% 0.22/0.50  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.50  thf('43', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '42'])).
% 0.22/0.50  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
