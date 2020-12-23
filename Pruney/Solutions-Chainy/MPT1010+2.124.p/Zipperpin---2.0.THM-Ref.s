%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5RchbJK41v

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 (  93 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  541 ( 785 expanded)
%              Number of equality atoms :   53 (  71 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X48 @ X45 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C )
      = sk_B ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ( k1_funct_1 @ sk_D @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X40: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X38: $i] :
      ( ( ( k10_relat_1 @ X38 @ ( k2_relat_1 @ X38 ) )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X39: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X40: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k2_relat_1 @ X43 ) )
      | ( ( k10_relat_1 @ X43 @ ( k1_tarski @ X44 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_tarski @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k1_tarski @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k1_tarski @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5RchbJK41v
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:12:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 108 iterations in 0.060s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(d1_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, axiom,
% 0.20/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.55          | ((X1) = (X2))
% 0.20/0.55          | ((X1) = (X3))
% 0.20/0.55          | ((X1) = (X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t65_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.55            ( m1_subset_1 @
% 0.20/0.55              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.55          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.55  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf(t7_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X45 @ X46)
% 0.20/0.55          | ((X47) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X48)
% 0.20/0.55          | ~ (v1_funct_2 @ X48 @ X46 @ X47)
% 0.20/0.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.20/0.55          | (r2_hidden @ (k1_funct_1 @ X48 @ X45) @ X47))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.20/0.55          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ (k1_tarski @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.55  thf(t69_enumset1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.55  thf('9', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf(t70_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.55  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_3, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.55          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.55          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.55         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.55          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ~ (zip_tseitin_0 @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B @ sk_B @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B))
% 0.20/0.55        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.55        | ((k1_funct_1 @ sk_D @ sk_C) = (sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.55  thf('18', plain, (((k1_funct_1 @ sk_D @ sk_C) != (sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('19', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf(t71_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.55  thf('21', plain, (![X40 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf(t169_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X38 : $i]:
% 0.20/0.55         (((k10_relat_1 @ X38 @ (k2_relat_1 @ X38)) = (k1_relat_1 @ X38))
% 0.20/0.55          | ~ (v1_relat_1 @ X38))),
% 0.20/0.55      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.20/0.55            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain, (![X39 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X39)) = (X39))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf(fc3_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('25', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.55  thf('27', plain, (![X40 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.20/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.55  thf(t142_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.55         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X43 : $i, X44 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X44 @ (k2_relat_1 @ X43))
% 0.20/0.55          | ((k10_relat_1 @ X43 @ (k1_tarski @ X44)) != (k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X43))),
% 0.20/0.55      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.55          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_tarski @ X1))
% 0.20/0.55              != (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X1 @ X0)
% 0.20/0.55          | ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k1_tarski @ X1))
% 0.20/0.55              != (k1_xboole_0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_tarski @ X0) != (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 0.20/0.55          | ((k1_tarski @ X0) != (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.55          | (r2_hidden @ X5 @ X9)
% 0.20/0.55          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.20/0.55          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.20/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['34', '36'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.55  thf('41', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['33', '40'])).
% 0.20/0.55  thf('42', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '41'])).
% 0.20/0.55  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
