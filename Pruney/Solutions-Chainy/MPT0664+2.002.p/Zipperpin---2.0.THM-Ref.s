%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7uSQ53hy5y

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:50 EST 2020

% Result     : Theorem 10.53s
% Output     : Refutation 10.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 103 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   20
%              Number of atoms          :  734 ( 986 expanded)
%              Number of equality atoms :   46 (  64 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ B )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_funct_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v1_relat_1 @ X66 )
      | ~ ( v1_funct_1 @ X66 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X67 @ X66 ) @ X68 )
        = ( k1_funct_1 @ X66 @ ( k1_funct_1 @ X67 @ X68 ) ) )
      | ~ ( r2_hidden @ X68 @ ( k1_relat_1 @ X67 ) )
      | ~ ( v1_funct_1 @ X67 )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X61: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('6',plain,(
    ! [X62: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X47: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r2_hidden @ X49 @ ( k1_relat_1 @ X51 ) )
      | ( r2_hidden @ X49 @ ( k1_relat_1 @ ( k7_relat_1 @ X51 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X61: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ sk_B ) ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ X52 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X52 ) @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t40_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('25',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( r2_hidden @ X69 @ ( k1_relat_1 @ ( k5_relat_1 @ X70 @ ( k6_relat_1 @ X71 ) ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X70 @ X69 ) @ X71 )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X61: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('28',plain,(
    ! [X61: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X62: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ X0 @ X1 @ X2 )
      | ( r2_hidden @ sk_A @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ sk_A @ ( k1_enumset1 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) )
      | ( sk_A = X0 )
      | ( sk_A = X1 ) ) ),
    inference('sup-',[status(thm)],['9','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_A = X0 )
      | ( sk_A
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(eq_fact,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) )
      | ( sk_A = X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( sk_A
    = ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_3 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_C_3 @ sk_A )
     != ( k1_funct_1 @ sk_C_3 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ( k1_funct_1 @ sk_C_3 @ sk_A )
 != ( k1_funct_1 @ sk_C_3 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7uSQ53hy5y
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:08:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 10.53/10.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.53/10.75  % Solved by: fo/fo7.sh
% 10.53/10.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.53/10.75  % done 9198 iterations in 10.300s
% 10.53/10.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.53/10.75  % SZS output start Refutation
% 10.53/10.75  thf(sk_A_type, type, sk_A: $i).
% 10.53/10.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.53/10.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.53/10.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.53/10.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 10.53/10.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 10.53/10.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.53/10.75  thf(sk_B_type, type, sk_B: $i).
% 10.53/10.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.53/10.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 10.53/10.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.53/10.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 10.53/10.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 10.53/10.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.53/10.75  thf(sk_C_3_type, type, sk_C_3: $i).
% 10.53/10.75  thf(t94_relat_1, axiom,
% 10.53/10.75    (![A:$i,B:$i]:
% 10.53/10.75     ( ( v1_relat_1 @ B ) =>
% 10.53/10.75       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 10.53/10.75  thf('0', plain,
% 10.53/10.75      (![X52 : $i, X53 : $i]:
% 10.53/10.75         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 10.53/10.75          | ~ (v1_relat_1 @ X53))),
% 10.53/10.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.75  thf(t72_funct_1, conjecture,
% 10.53/10.75    (![A:$i,B:$i,C:$i]:
% 10.53/10.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.53/10.75       ( ( r2_hidden @ A @ B ) =>
% 10.53/10.75         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 10.53/10.75  thf(zf_stmt_0, negated_conjecture,
% 10.53/10.75    (~( ![A:$i,B:$i,C:$i]:
% 10.53/10.75        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.53/10.75          ( ( r2_hidden @ A @ B ) =>
% 10.53/10.75            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 10.53/10.75              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 10.53/10.75    inference('cnf.neg', [status(esa)], [t72_funct_1])).
% 10.53/10.75  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf(t71_relat_1, axiom,
% 10.53/10.75    (![A:$i]:
% 10.53/10.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 10.53/10.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 10.53/10.75  thf('2', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 10.53/10.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.75  thf(t23_funct_1, axiom,
% 10.53/10.75    (![A:$i,B:$i]:
% 10.53/10.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.53/10.75       ( ![C:$i]:
% 10.53/10.75         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.53/10.75           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 10.53/10.75             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 10.53/10.75               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 10.53/10.75  thf('3', plain,
% 10.53/10.75      (![X66 : $i, X67 : $i, X68 : $i]:
% 10.53/10.75         (~ (v1_relat_1 @ X66)
% 10.53/10.75          | ~ (v1_funct_1 @ X66)
% 10.53/10.75          | ((k1_funct_1 @ (k5_relat_1 @ X67 @ X66) @ X68)
% 10.53/10.75              = (k1_funct_1 @ X66 @ (k1_funct_1 @ X67 @ X68)))
% 10.53/10.75          | ~ (r2_hidden @ X68 @ (k1_relat_1 @ X67))
% 10.53/10.75          | ~ (v1_funct_1 @ X67)
% 10.53/10.75          | ~ (v1_relat_1 @ X67))),
% 10.53/10.75      inference('cnf', [status(esa)], [t23_funct_1])).
% 10.53/10.75  thf('4', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X1 @ X0)
% 10.53/10.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.75          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.75          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 10.53/10.75              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 10.53/10.75          | ~ (v1_funct_1 @ X2)
% 10.53/10.75          | ~ (v1_relat_1 @ X2))),
% 10.53/10.75      inference('sup-', [status(thm)], ['2', '3'])).
% 10.53/10.75  thf(fc3_funct_1, axiom,
% 10.53/10.75    (![A:$i]:
% 10.53/10.75     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 10.53/10.75       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 10.53/10.75  thf('5', plain, (![X61 : $i]: (v1_relat_1 @ (k6_relat_1 @ X61))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('6', plain, (![X62 : $i]: (v1_funct_1 @ (k6_relat_1 @ X62))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('7', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X1 @ X0)
% 10.53/10.75          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 10.53/10.75              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 10.53/10.75          | ~ (v1_funct_1 @ X2)
% 10.53/10.75          | ~ (v1_relat_1 @ X2))),
% 10.53/10.75      inference('demod', [status(thm)], ['4', '5', '6'])).
% 10.53/10.75  thf('8', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (~ (v1_relat_1 @ X0)
% 10.53/10.75          | ~ (v1_funct_1 @ X0)
% 10.53/10.75          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 10.53/10.75              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 10.53/10.75      inference('sup-', [status(thm)], ['1', '7'])).
% 10.53/10.75  thf(d1_enumset1, axiom,
% 10.53/10.75    (![A:$i,B:$i,C:$i,D:$i]:
% 10.53/10.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 10.53/10.75       ( ![E:$i]:
% 10.53/10.75         ( ( r2_hidden @ E @ D ) <=>
% 10.53/10.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 10.53/10.75  thf(zf_stmt_1, axiom,
% 10.53/10.75    (![E:$i,C:$i,B:$i,A:$i]:
% 10.53/10.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 10.53/10.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 10.53/10.75  thf('9', plain,
% 10.53/10.75      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 10.53/10.75         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 10.53/10.75          | ((X11) = (X12))
% 10.53/10.75          | ((X11) = (X13))
% 10.53/10.75          | ((X11) = (X14)))),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.53/10.75  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 10.53/10.75  thf(zf_stmt_3, axiom,
% 10.53/10.75    (![A:$i,B:$i,C:$i,D:$i]:
% 10.53/10.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 10.53/10.75       ( ![E:$i]:
% 10.53/10.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 10.53/10.75  thf('10', plain,
% 10.53/10.75      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 10.53/10.75         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 10.53/10.75          | (r2_hidden @ X15 @ X19)
% 10.53/10.75          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.53/10.75  thf('11', plain,
% 10.53/10.75      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 10.53/10.75         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 10.53/10.75          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 10.53/10.75      inference('simplify', [status(thm)], ['10'])).
% 10.53/10.75  thf('12', plain, ((r2_hidden @ sk_A @ sk_B)),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf('13', plain, ((r2_hidden @ sk_A @ sk_B)),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf(d5_xboole_0, axiom,
% 10.53/10.75    (![A:$i,B:$i,C:$i]:
% 10.53/10.75     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 10.53/10.75       ( ![D:$i]:
% 10.53/10.75         ( ( r2_hidden @ D @ C ) <=>
% 10.53/10.75           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 10.53/10.75  thf('14', plain,
% 10.53/10.75      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X4 @ X5)
% 10.53/10.75          | (r2_hidden @ X4 @ X6)
% 10.53/10.75          | (r2_hidden @ X4 @ X7)
% 10.53/10.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 10.53/10.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 10.53/10.75  thf('15', plain,
% 10.53/10.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.53/10.75         ((r2_hidden @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 10.53/10.75          | (r2_hidden @ X4 @ X6)
% 10.53/10.75          | ~ (r2_hidden @ X4 @ X5))),
% 10.53/10.75      inference('simplify', [status(thm)], ['14'])).
% 10.53/10.75  thf('16', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         ((r2_hidden @ sk_A @ X0)
% 10.53/10.75          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 10.53/10.75      inference('sup-', [status(thm)], ['13', '15'])).
% 10.53/10.75  thf('17', plain, (![X47 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 10.53/10.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 10.53/10.75  thf(t86_relat_1, axiom,
% 10.53/10.75    (![A:$i,B:$i,C:$i]:
% 10.53/10.75     ( ( v1_relat_1 @ C ) =>
% 10.53/10.75       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 10.53/10.75         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 10.53/10.75  thf('18', plain,
% 10.53/10.75      (![X49 : $i, X50 : $i, X51 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X49 @ X50)
% 10.53/10.75          | ~ (r2_hidden @ X49 @ (k1_relat_1 @ X51))
% 10.53/10.75          | (r2_hidden @ X49 @ (k1_relat_1 @ (k7_relat_1 @ X51 @ X50)))
% 10.53/10.75          | ~ (v1_relat_1 @ X51))),
% 10.53/10.75      inference('cnf', [status(esa)], [t86_relat_1])).
% 10.53/10.75  thf('19', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X1 @ X0)
% 10.53/10.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.75          | (r2_hidden @ X1 @ 
% 10.53/10.75             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 10.53/10.75          | ~ (r2_hidden @ X1 @ X2))),
% 10.53/10.75      inference('sup-', [status(thm)], ['17', '18'])).
% 10.53/10.75  thf('20', plain, (![X61 : $i]: (v1_relat_1 @ (k6_relat_1 @ X61))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('21', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X1 @ X0)
% 10.53/10.75          | (r2_hidden @ X1 @ 
% 10.53/10.75             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X2)))
% 10.53/10.75          | ~ (r2_hidden @ X1 @ X2))),
% 10.53/10.75      inference('demod', [status(thm)], ['19', '20'])).
% 10.53/10.75  thf('22', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i]:
% 10.53/10.75         ((r2_hidden @ sk_A @ X0)
% 10.53/10.75          | ~ (r2_hidden @ sk_A @ X1)
% 10.53/10.75          | (r2_hidden @ sk_A @ 
% 10.53/10.75             (k1_relat_1 @ 
% 10.53/10.75              (k7_relat_1 @ (k6_relat_1 @ (k4_xboole_0 @ sk_B @ X0)) @ X1))))),
% 10.53/10.75      inference('sup-', [status(thm)], ['16', '21'])).
% 10.53/10.75  thf('23', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         ((r2_hidden @ sk_A @ 
% 10.53/10.75           (k1_relat_1 @ 
% 10.53/10.75            (k7_relat_1 @ (k6_relat_1 @ (k4_xboole_0 @ sk_B @ X0)) @ sk_B)))
% 10.53/10.75          | (r2_hidden @ sk_A @ X0))),
% 10.53/10.75      inference('sup-', [status(thm)], ['12', '22'])).
% 10.53/10.75  thf('24', plain,
% 10.53/10.75      (![X52 : $i, X53 : $i]:
% 10.53/10.75         (((k7_relat_1 @ X53 @ X52) = (k5_relat_1 @ (k6_relat_1 @ X52) @ X53))
% 10.53/10.75          | ~ (v1_relat_1 @ X53))),
% 10.53/10.75      inference('cnf', [status(esa)], [t94_relat_1])).
% 10.53/10.75  thf(t40_funct_1, axiom,
% 10.53/10.75    (![A:$i,B:$i,C:$i]:
% 10.53/10.75     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.53/10.75       ( ( r2_hidden @
% 10.53/10.75           A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ ( k6_relat_1 @ B ) ) ) ) <=>
% 10.53/10.75         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 10.53/10.75           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 10.53/10.75  thf('25', plain,
% 10.53/10.75      (![X69 : $i, X70 : $i, X71 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X69 @ 
% 10.53/10.75             (k1_relat_1 @ (k5_relat_1 @ X70 @ (k6_relat_1 @ X71))))
% 10.53/10.75          | (r2_hidden @ (k1_funct_1 @ X70 @ X69) @ X71)
% 10.53/10.75          | ~ (v1_funct_1 @ X70)
% 10.53/10.75          | ~ (v1_relat_1 @ X70))),
% 10.53/10.75      inference('cnf', [status(esa)], [t40_funct_1])).
% 10.53/10.75  thf('26', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X2 @ 
% 10.53/10.75             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 10.53/10.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 10.53/10.75          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 10.53/10.75          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 10.53/10.75          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2) @ X1))),
% 10.53/10.75      inference('sup-', [status(thm)], ['24', '25'])).
% 10.53/10.75  thf('27', plain, (![X61 : $i]: (v1_relat_1 @ (k6_relat_1 @ X61))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('28', plain, (![X61 : $i]: (v1_relat_1 @ (k6_relat_1 @ X61))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('29', plain, (![X62 : $i]: (v1_funct_1 @ (k6_relat_1 @ X62))),
% 10.53/10.75      inference('cnf', [status(esa)], [fc3_funct_1])).
% 10.53/10.75  thf('30', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X2 @ 
% 10.53/10.75             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)))
% 10.53/10.75          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X2) @ X1))),
% 10.53/10.75      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 10.53/10.75  thf('31', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         ((r2_hidden @ sk_A @ X0)
% 10.53/10.75          | (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ 
% 10.53/10.75             (k4_xboole_0 @ sk_B @ X0)))),
% 10.53/10.75      inference('sup-', [status(thm)], ['23', '30'])).
% 10.53/10.75  thf('32', plain,
% 10.53/10.75      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X8 @ X7)
% 10.53/10.75          | ~ (r2_hidden @ X8 @ X6)
% 10.53/10.75          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 10.53/10.75      inference('cnf', [status(esa)], [d5_xboole_0])).
% 10.53/10.75  thf('33', plain,
% 10.53/10.75      (![X5 : $i, X6 : $i, X8 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X8 @ X6)
% 10.53/10.75          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 10.53/10.75      inference('simplify', [status(thm)], ['32'])).
% 10.53/10.75  thf('34', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         ((r2_hidden @ sk_A @ X0)
% 10.53/10.75          | ~ (r2_hidden @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ X0))),
% 10.53/10.75      inference('sup-', [status(thm)], ['31', '33'])).
% 10.53/10.75  thf('35', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.53/10.75         ((zip_tseitin_0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ X0 @ 
% 10.53/10.75           X1 @ X2)
% 10.53/10.75          | (r2_hidden @ sk_A @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 10.53/10.75      inference('sup-', [status(thm)], ['11', '34'])).
% 10.53/10.75  thf('36', plain,
% 10.53/10.75      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 10.53/10.75         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.53/10.75  thf('37', plain,
% 10.53/10.75      (![X10 : $i, X12 : $i, X13 : $i]:
% 10.53/10.75         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 10.53/10.75      inference('simplify', [status(thm)], ['36'])).
% 10.53/10.75  thf('38', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i]:
% 10.53/10.75         (r2_hidden @ sk_A @ 
% 10.53/10.75          (k1_enumset1 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) @ X0 @ X1))),
% 10.53/10.75      inference('sup-', [status(thm)], ['35', '37'])).
% 10.53/10.75  thf('39', plain,
% 10.53/10.75      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 10.53/10.75         (~ (r2_hidden @ X20 @ X19)
% 10.53/10.75          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 10.53/10.75          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.53/10.75  thf('40', plain,
% 10.53/10.75      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 10.53/10.75         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 10.53/10.75          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 10.53/10.75      inference('simplify', [status(thm)], ['39'])).
% 10.53/10.75  thf('41', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i]:
% 10.53/10.75         ~ (zip_tseitin_0 @ sk_A @ X0 @ X1 @ 
% 10.53/10.75            (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 10.53/10.75      inference('sup-', [status(thm)], ['38', '40'])).
% 10.53/10.75  thf('42', plain,
% 10.53/10.75      (![X0 : $i, X1 : $i]:
% 10.53/10.75         (((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))
% 10.53/10.75          | ((sk_A) = (X0))
% 10.53/10.75          | ((sk_A) = (X1)))),
% 10.53/10.75      inference('sup-', [status(thm)], ['9', '41'])).
% 10.53/10.75  thf('43', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (((sk_A) != (sk_A))
% 10.53/10.75          | ((sk_A) = (X0))
% 10.53/10.75          | ((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A)))),
% 10.53/10.75      inference('eq_fact', [status(thm)], ['42'])).
% 10.53/10.75  thf('44', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))
% 10.53/10.75          | ((sk_A) = (X0)))),
% 10.53/10.75      inference('simplify', [status(thm)], ['43'])).
% 10.53/10.75  thf('45', plain, (((sk_A) = (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))),
% 10.53/10.75      inference('condensation', [status(thm)], ['44'])).
% 10.53/10.75  thf('46', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (~ (v1_relat_1 @ X0)
% 10.53/10.75          | ~ (v1_funct_1 @ X0)
% 10.53/10.75          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 10.53/10.75              = (k1_funct_1 @ X0 @ sk_A)))),
% 10.53/10.75      inference('demod', [status(thm)], ['8', '45'])).
% 10.53/10.75  thf('47', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 10.53/10.75            = (k1_funct_1 @ X0 @ sk_A))
% 10.53/10.75          | ~ (v1_relat_1 @ X0)
% 10.53/10.75          | ~ (v1_funct_1 @ X0)
% 10.53/10.75          | ~ (v1_relat_1 @ X0))),
% 10.53/10.75      inference('sup+', [status(thm)], ['0', '46'])).
% 10.53/10.75  thf('48', plain,
% 10.53/10.75      (![X0 : $i]:
% 10.53/10.75         (~ (v1_funct_1 @ X0)
% 10.53/10.75          | ~ (v1_relat_1 @ X0)
% 10.53/10.75          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 10.53/10.75              = (k1_funct_1 @ X0 @ sk_A)))),
% 10.53/10.75      inference('simplify', [status(thm)], ['47'])).
% 10.53/10.75  thf('49', plain,
% 10.53/10.75      (((k1_funct_1 @ (k7_relat_1 @ sk_C_3 @ sk_B) @ sk_A)
% 10.53/10.75         != (k1_funct_1 @ sk_C_3 @ sk_A))),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf('50', plain,
% 10.53/10.75      ((((k1_funct_1 @ sk_C_3 @ sk_A) != (k1_funct_1 @ sk_C_3 @ sk_A))
% 10.53/10.75        | ~ (v1_relat_1 @ sk_C_3)
% 10.53/10.75        | ~ (v1_funct_1 @ sk_C_3))),
% 10.53/10.75      inference('sup-', [status(thm)], ['48', '49'])).
% 10.53/10.75  thf('51', plain, ((v1_relat_1 @ sk_C_3)),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf('52', plain, ((v1_funct_1 @ sk_C_3)),
% 10.53/10.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.53/10.75  thf('53', plain,
% 10.53/10.75      (((k1_funct_1 @ sk_C_3 @ sk_A) != (k1_funct_1 @ sk_C_3 @ sk_A))),
% 10.53/10.75      inference('demod', [status(thm)], ['50', '51', '52'])).
% 10.53/10.75  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 10.53/10.75  
% 10.53/10.75  % SZS output end Refutation
% 10.53/10.75  
% 10.53/10.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
