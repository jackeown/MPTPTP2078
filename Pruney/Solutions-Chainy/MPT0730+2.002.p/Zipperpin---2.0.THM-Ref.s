%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EydGwaBP7q

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 347 expanded)
%              Number of leaves         :   37 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  702 (2569 expanded)
%              Number of equality atoms :   47 ( 201 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( r2_hidden @ X49 @ ( k1_ordinal1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('18',plain,(
    ! [X48: $i] :
      ( ( k1_ordinal1 @ X48 )
      = ( k2_xboole_0 @ X48 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,(
    ! [X48: $i] :
      ( ( k1_ordinal1 @ X48 )
      = ( k2_xboole_0 @ X48 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( zip_tseitin_0 @ X14 @ X13 @ X12 )
      | ( zip_tseitin_1 @ X14 @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ ( k1_tarski @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_tarski @ X0 ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( X15 != X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( r2_hidden @ X35 @ X34 )
      | ( X34
        = ( k4_xboole_0 @ X34 @ ( k2_tarski @ X33 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r1_tarski @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X22 )
      | ( ( k4_xboole_0 @ X20 @ X22 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ ( k1_tarski @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_tarski @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['29','41'])).

thf('43',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('45',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['46','48'])).

thf('50',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('52',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_tarski @ X29 @ ( k3_tarski @ X30 ) )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('54',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('58',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X15: $i,X17: $i] :
      ( ( X15 = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('64',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i] :
      ( r1_tarski @ X16 @ X16 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('66',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('67',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ X45 @ X47 )
      | ( r1_tarski @ ( k1_setfam_1 @ X46 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['64','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EydGwaBP7q
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:30:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 805 iterations in 0.380s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.60/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.60/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.60/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.60/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(t13_ordinal1, conjecture,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.60/0.83       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i,B:$i]:
% 0.60/0.83        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.60/0.83          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 0.60/0.83  thf('0', plain,
% 0.60/0.83      ((((sk_A) = (sk_B))
% 0.60/0.83        | (r2_hidden @ sk_A @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.60/0.83         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['0'])).
% 0.60/0.83  thf('2', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.60/0.83        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['2'])).
% 0.60/0.83  thf('4', plain,
% 0.60/0.83      ((((sk_A) = (sk_B))
% 0.60/0.83        | (r2_hidden @ sk_A @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('5', plain,
% 0.60/0.83      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('6', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['5'])).
% 0.60/0.83  thf('7', plain,
% 0.60/0.83      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('split', [status(esa)], ['5'])).
% 0.60/0.83  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.60/0.83  thf('8', plain, (![X49 : $i]: (r2_hidden @ X49 @ (k1_ordinal1 @ X49))),
% 0.60/0.83      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.60/0.83  thf('9', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['0'])).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['2'])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.60/0.83             (((sk_A) = (sk_B))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['8', '11'])).
% 0.60/0.83  thf('13', plain, (~ (((sk_A) = (sk_B)))),
% 0.60/0.83      inference('sat_resolution*', [status(thm)], ['7', '12'])).
% 0.60/0.83  thf('14', plain, (((sk_A) != (sk_B))),
% 0.60/0.83      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.60/0.83  thf('15', plain,
% 0.60/0.83      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('simplify_reflect-', [status(thm)], ['4', '14'])).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('split', [status(esa)], ['2'])).
% 0.60/0.83  thf('17', plain,
% 0.60/0.83      (((r2_hidden @ sk_A @ sk_B))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.83  thf(d1_ordinal1, axiom,
% 0.60/0.83    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.60/0.83  thf('18', plain,
% 0.60/0.83      (![X48 : $i]:
% 0.60/0.83         ((k1_ordinal1 @ X48) = (k2_xboole_0 @ X48 @ (k1_tarski @ X48)))),
% 0.60/0.83      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.60/0.83  thf(t7_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.83  thf('19', plain,
% 0.60/0.83      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.60/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.60/0.83  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.60/0.83  thf(d3_tarski, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.83          | (r2_hidden @ X0 @ X2)
% 0.60/0.83          | ~ (r1_tarski @ X1 @ X2))),
% 0.60/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.83  thf('22', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.60/0.83         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.60/0.83      inference('sup-', [status(thm)], ['17', '22'])).
% 0.60/0.83  thf('24', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('demod', [status(thm)], ['3', '23'])).
% 0.60/0.83  thf('25', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('sat_resolution*', [status(thm)], ['24'])).
% 0.60/0.83  thf('26', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 0.60/0.83      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.60/0.83  thf('27', plain,
% 0.60/0.83      (![X48 : $i]:
% 0.60/0.83         ((k1_ordinal1 @ X48) = (k2_xboole_0 @ X48 @ (k1_tarski @ X48)))),
% 0.60/0.83      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.60/0.83  thf(t5_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.60/0.83          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.83          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.60/0.83  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.83  thf(zf_stmt_2, axiom,
% 0.60/0.83    (![C:$i,B:$i,A:$i]:
% 0.60/0.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.83       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.60/0.83  thf(zf_stmt_4, axiom,
% 0.60/0.83    (![C:$i,B:$i,A:$i]:
% 0.60/0.83     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.60/0.83       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.60/0.83  thf(zf_stmt_5, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.60/0.83          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.60/0.83          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.83          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.60/0.83  thf('28', plain,
% 0.60/0.83      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.83         (~ (r1_xboole_0 @ X12 @ X13)
% 0.60/0.83          | (zip_tseitin_0 @ X14 @ X13 @ X12)
% 0.60/0.83          | (zip_tseitin_1 @ X14 @ X13 @ X12)
% 0.60/0.83          | ~ (r2_hidden @ X14 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.83  thf('29', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.60/0.83          | (zip_tseitin_1 @ X1 @ (k1_tarski @ X0) @ X0)
% 0.60/0.83          | (zip_tseitin_0 @ X1 @ (k1_tarski @ X0) @ X0)
% 0.60/0.83          | ~ (r1_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.83  thf(d10_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.83  thf('30', plain,
% 0.60/0.83      (![X15 : $i, X16 : $i]: ((r1_tarski @ X15 @ X16) | ((X15) != (X16)))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('31', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.60/0.83      inference('simplify', [status(thm)], ['30'])).
% 0.60/0.83  thf(t69_enumset1, axiom,
% 0.60/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.83  thf('32', plain,
% 0.60/0.83      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.60/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.83  thf(t144_zfmisc_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.60/0.83          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.60/0.83  thf('33', plain,
% 0.60/0.83      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.83         ((r2_hidden @ X33 @ X34)
% 0.60/0.83          | (r2_hidden @ X35 @ X34)
% 0.60/0.83          | ((X34) = (k4_xboole_0 @ X34 @ (k2_tarski @ X33 @ X35))))),
% 0.60/0.83      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.60/0.83  thf('34', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.60/0.83          | (r2_hidden @ X0 @ X1)
% 0.60/0.83          | (r2_hidden @ X0 @ X1))),
% 0.60/0.83      inference('sup+', [status(thm)], ['32', '33'])).
% 0.60/0.83  thf('35', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         ((r2_hidden @ X0 @ X1)
% 0.60/0.83          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.60/0.83      inference('simplify', [status(thm)], ['34'])).
% 0.60/0.83  thf(t7_ordinal1, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.83  thf('36', plain,
% 0.60/0.83      (![X50 : $i, X51 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X50 @ X51) | ~ (r1_tarski @ X51 @ X50))),
% 0.60/0.83      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.83  thf('37', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.60/0.83          | ~ (r1_tarski @ X0 @ X1))),
% 0.60/0.83      inference('sup-', [status(thm)], ['35', '36'])).
% 0.60/0.83  thf('38', plain,
% 0.60/0.83      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['31', '37'])).
% 0.60/0.83  thf(t83_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.83  thf('39', plain,
% 0.60/0.83      (![X20 : $i, X22 : $i]:
% 0.60/0.83         ((r1_xboole_0 @ X20 @ X22) | ((k4_xboole_0 @ X20 @ X22) != (X20)))),
% 0.60/0.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.60/0.83  thf('40', plain,
% 0.60/0.83      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ (k1_tarski @ X0)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.60/0.83  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ X0))),
% 0.60/0.83      inference('simplify', [status(thm)], ['40'])).
% 0.60/0.83  thf('42', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.60/0.83          | (zip_tseitin_1 @ X1 @ (k1_tarski @ X0) @ X0)
% 0.60/0.83          | (zip_tseitin_0 @ X1 @ (k1_tarski @ X0) @ X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['29', '41'])).
% 0.60/0.83  thf('43', plain,
% 0.60/0.83      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 0.60/0.83        | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['26', '42'])).
% 0.60/0.83  thf('44', plain,
% 0.60/0.83      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.83         ((r2_hidden @ X9 @ X10) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.83  thf('45', plain,
% 0.60/0.83      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 0.60/0.83        | (r2_hidden @ sk_A @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.83  thf('46', plain,
% 0.60/0.83      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.60/0.83      inference('split', [status(esa)], ['2'])).
% 0.60/0.83  thf('47', plain,
% 0.60/0.83      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.60/0.83       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.60/0.83      inference('split', [status(esa)], ['2'])).
% 0.60/0.83  thf('48', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.60/0.83      inference('sat_resolution*', [status(thm)], ['24', '47'])).
% 0.60/0.83  thf('49', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.60/0.83      inference('simpl_trail', [status(thm)], ['46', '48'])).
% 0.60/0.83  thf('50', plain, ((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)),
% 0.60/0.83      inference('clc', [status(thm)], ['45', '49'])).
% 0.60/0.83  thf('51', plain,
% 0.60/0.83      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.83         ((r2_hidden @ X6 @ X7) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.60/0.83  thf('52', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.83  thf(l49_zfmisc_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.60/0.83  thf('53', plain,
% 0.60/0.83      (![X29 : $i, X30 : $i]:
% 0.60/0.83         ((r1_tarski @ X29 @ (k3_tarski @ X30)) | ~ (r2_hidden @ X29 @ X30))),
% 0.60/0.83      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.60/0.83  thf('54', plain, ((r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.60/0.83  thf('55', plain,
% 0.60/0.83      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.60/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.83  thf(l51_zfmisc_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.83  thf('56', plain,
% 0.60/0.83      (![X31 : $i, X32 : $i]:
% 0.60/0.83         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 0.60/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.60/0.83  thf('57', plain,
% 0.60/0.83      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['55', '56'])).
% 0.60/0.83  thf(idempotence_k2_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.60/0.83  thf('58', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 0.60/0.83      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.60/0.83  thf('59', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['57', '58'])).
% 0.60/0.83  thf('60', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.60/0.83      inference('demod', [status(thm)], ['54', '59'])).
% 0.60/0.83  thf('61', plain,
% 0.60/0.83      (![X15 : $i, X17 : $i]:
% 0.60/0.83         (((X15) = (X17))
% 0.60/0.83          | ~ (r1_tarski @ X17 @ X15)
% 0.60/0.83          | ~ (r1_tarski @ X15 @ X17))),
% 0.60/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.83  thf('62', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['60', '61'])).
% 0.60/0.83  thf('63', plain, (((sk_A) != (sk_B))),
% 0.60/0.83      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 0.60/0.83  thf('64', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.60/0.83      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.60/0.83  thf('65', plain, (![X16 : $i]: (r1_tarski @ X16 @ X16)),
% 0.60/0.83      inference('simplify', [status(thm)], ['30'])).
% 0.60/0.83  thf('66', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.60/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.83  thf(t8_setfam_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.60/0.83       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.60/0.83  thf('67', plain,
% 0.60/0.83      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.60/0.83         (~ (r2_hidden @ X45 @ X46)
% 0.60/0.83          | ~ (r1_tarski @ X45 @ X47)
% 0.60/0.83          | (r1_tarski @ (k1_setfam_1 @ X46) @ X47))),
% 0.60/0.83      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.60/0.83  thf('68', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_B)) @ X0)
% 0.60/0.83          | ~ (r1_tarski @ sk_A @ X0))),
% 0.60/0.83      inference('sup-', [status(thm)], ['66', '67'])).
% 0.60/0.83  thf('69', plain,
% 0.60/0.83      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.60/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.83  thf(t12_setfam_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.60/0.83  thf('70', plain,
% 0.60/0.83      (![X38 : $i, X39 : $i]:
% 0.60/0.83         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.60/0.83      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.60/0.83  thf('71', plain,
% 0.60/0.83      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['69', '70'])).
% 0.60/0.83  thf(idempotence_k3_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.60/0.83  thf('72', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.60/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.60/0.83  thf('73', plain, (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['71', '72'])).
% 0.60/0.83  thf('74', plain,
% 0.60/0.83      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.60/0.83      inference('demod', [status(thm)], ['68', '73'])).
% 0.60/0.83  thf('75', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.60/0.83      inference('sup-', [status(thm)], ['65', '74'])).
% 0.60/0.83  thf('76', plain, ($false), inference('demod', [status(thm)], ['64', '75'])).
% 0.60/0.83  
% 0.60/0.83  % SZS output end Refutation
% 0.60/0.83  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
