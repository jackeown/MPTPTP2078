%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EGaFh2fuPo

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:23 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  144 (1138 expanded)
%              Number of leaves         :   34 ( 340 expanded)
%              Depth                    :   27
%              Number of atoms          : 1243 (13000 expanded)
%              Number of equality atoms :  163 (1667 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X24 @ X30 )
      | ( X30
       != ( k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X24 @ ( k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X21 @ X22 @ X17 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      | ( X18 = X19 )
      | ( X18 = X20 )
      | ( X18 = X21 )
      | ( X18 = X22 )
      | ( X18 = X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k11_relat_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( r2_hidden @ X40 @ ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_enumset1 @ X6 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X25 @ X26 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X15 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ X39 ) )
      | ( ( k11_relat_1 @ X39 @ X40 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) )
        = sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_C @ X0 @ ( k1_tarski @ sk_A ) )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X15 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ X39 ) )
      | ( ( k11_relat_1 @ X39 @ X40 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_B @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X35: $i] :
      ( ( ( k9_relat_1 @ X35 @ ( k1_relat_1 @ X35 ) )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k11_relat_1 @ X33 @ X34 )
        = ( k9_relat_1 @ X33 @ ( k1_tarski @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('55',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X15 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('59',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k11_relat_1 @ X37 @ X38 ) )
      | ( r2_hidden @ ( k4_tarski @ X38 @ X36 ) @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('65',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X41 @ X43 ) @ X42 )
      | ( X43
        = ( k1_funct_1 @ X42 @ X41 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( sk_C @ X16 @ X15 )
       != X16 )
      | ( X15
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_B @ X1 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('85',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k11_relat_1 @ X33 @ X34 )
        = ( k9_relat_1 @ X33 @ ( k1_tarski @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_B @ X0 )
      = ( k9_relat_1 @ sk_B @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_B @ X0 )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_B @ X0 )
      = ( k9_relat_1 @ sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('93',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','74'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['82','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','95'])).

thf('97',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('100',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('103',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','96'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','74'])).

thf('107',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(simplify,[status(thm)],['107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EGaFh2fuPo
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:08:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 294 iterations in 0.167s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.43/0.61  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.43/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.43/0.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.43/0.61  thf(t70_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.61  thf(t71_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf(t72_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.61         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.43/0.61           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.61  thf(d3_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.61     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.43/0.61       ( ![G:$i]:
% 0.43/0.61         ( ( r2_hidden @ G @ F ) <=>
% 0.43/0.61           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.43/0.61                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_1, axiom,
% 0.43/0.61    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.43/0.61       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.43/0.61         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_2, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.61     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.43/0.61       ( ![G:$i]:
% 0.43/0.61         ( ( r2_hidden @ G @ F ) <=>
% 0.43/0.61           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.43/0.61         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.43/0.61          | (r2_hidden @ X24 @ X30)
% 0.43/0.61          | ((X30) != (k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.43/0.61         ((r2_hidden @ X24 @ (k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25))
% 0.43/0.61          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.43/0.61      inference('simplify', [status(thm)], ['3'])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.61          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.43/0.61      inference('sup+', [status(thm)], ['2', '4'])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         (((X18) != (X17))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X17 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.61         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X21 @ X22 @ X17)),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['1', '8'])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.43/0.61      inference('sup+', [status(thm)], ['0', '9'])).
% 0.43/0.61  thf(t69_enumset1, axiom,
% 0.43/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.61  thf('11', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.43/0.61         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.43/0.61          | ((X18) = (X19))
% 0.43/0.61          | ((X18) = (X20))
% 0.43/0.61          | ((X18) = (X21))
% 0.43/0.61          | ((X18) = (X22))
% 0.43/0.61          | ((X18) = (X23)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.61  thf(t14_funct_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.61       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.43/0.61         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_3, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i]:
% 0.43/0.61        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.43/0.61          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.43/0.61            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.43/0.61  thf('13', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf(t205_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ B ) =>
% 0.43/0.61       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.43/0.61         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X39 : $i, X40 : $i]:
% 0.43/0.61         (((k11_relat_1 @ X39 @ X40) = (k1_xboole_0))
% 0.43/0.61          | (r2_hidden @ X40 @ (k1_relat_1 @ X39))
% 0.43/0.61          | ~ (v1_relat_1 @ X39))),
% 0.43/0.61      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('18', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.43/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.61         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.61         ((k3_enumset1 @ X6 @ X6 @ X7 @ X8 @ X9)
% 0.43/0.61           = (k2_enumset1 @ X6 @ X7 @ X8 @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X31 @ X30)
% 0.43/0.61          | ~ (zip_tseitin_0 @ X31 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.43/0.61          | ((X30) != (k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.43/0.61         (~ (zip_tseitin_0 @ X31 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.43/0.61          | ~ (r2_hidden @ X31 @ (k3_enumset1 @ X29 @ X28 @ X27 @ X26 @ X25)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.43/0.61      inference('sup-', [status(thm)], ['21', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 @ X2))),
% 0.43/0.61      inference('sup-', [status(thm)], ['20', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 @ X1 @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['19', '25'])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['18', '26'])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.43/0.61          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['17', '27'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((X0) = (sk_A))
% 0.43/0.61          | ((X0) = (sk_A))
% 0.43/0.61          | ((X0) = (sk_A))
% 0.43/0.61          | ((X0) = (sk_A))
% 0.43/0.61          | ((X0) = (sk_A))
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['12', '28'])).
% 0.43/0.61  thf('30', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['29'])).
% 0.43/0.61  thf(t41_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.61          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (((X15) = (k1_xboole_0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X16 @ X15) @ X15)
% 0.43/0.61          | ((X15) = (k1_tarski @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X39 : $i, X40 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X40 @ (k1_relat_1 @ X39))
% 0.43/0.61          | ((k11_relat_1 @ X39 @ X40) != (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X39))),
% 0.43/0.61      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 0.43/0.61          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X0)
% 0.43/0.61          | ((k11_relat_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0)))
% 0.43/0.61              != (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61          | ((sk_C @ X0 @ (k1_relat_1 @ sk_B)) = (sk_A))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.61          | ((k1_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61          | ((k1_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '33'])).
% 0.43/0.61  thf('35', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('37', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('38', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61          | ((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_A))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((sk_C @ X0 @ (k1_tarski @ sk_A)) = (sk_A)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (((X15) = (k1_xboole_0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X16 @ X15) @ X15)
% 0.43/0.61          | ((X15) = (k1_tarski @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.43/0.61  thf('42', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X39 : $i, X40 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X40 @ (k1_relat_1 @ X39))
% 0.43/0.61          | ((k11_relat_1 @ X39 @ X40) != (k1_xboole_0))
% 0.43/0.61          | ~ (v1_relat_1 @ X39))),
% 0.43/0.61      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.43/0.61  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ (sk_C @ X0 @ (k1_tarski @ sk_A)))
% 0.43/0.61              != (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['41', '46'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '47'])).
% 0.43/0.61  thf('49', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf(t146_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (![X35 : $i]:
% 0.43/0.61         (((k9_relat_1 @ X35 @ (k1_relat_1 @ X35)) = (k2_relat_1 @ X35))
% 0.43/0.61          | ~ (v1_relat_1 @ X35))),
% 0.43/0.61      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['49', '50'])).
% 0.43/0.61  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf(d16_relat_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X33 : $i, X34 : $i]:
% 0.43/0.61         (((k11_relat_1 @ X33 @ X34) = (k9_relat_1 @ X33 @ (k1_tarski @ X34)))
% 0.43/0.61          | ~ (v1_relat_1 @ X33))),
% 0.43/0.61      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.43/0.61        | ~ (v1_relat_1 @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('57', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (((X15) = (k1_xboole_0))
% 0.43/0.61          | (r2_hidden @ (sk_C @ X16 @ X15) @ X15)
% 0.43/0.61          | ((X15) = (k1_tarski @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.43/0.61  thf('59', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.43/0.61  thf(t204_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( v1_relat_1 @ C ) =>
% 0.43/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.43/0.61         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X36 @ (k11_relat_1 @ X37 @ X38))
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ X38 @ X36) @ X37)
% 0.43/0.61          | ~ (v1_relat_1 @ X37))),
% 0.43/0.61      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['59', '60'])).
% 0.43/0.61  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.43/0.61          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['61', '62'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['58', '63'])).
% 0.43/0.61  thf(t8_funct_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.43/0.61       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.43/0.61         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.43/0.61           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.43/0.61  thf('65', plain,
% 0.43/0.61      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k4_tarski @ X41 @ X43) @ X42)
% 0.43/0.61          | ((X43) = (k1_funct_1 @ X42 @ X41))
% 0.43/0.61          | ~ (v1_funct_1 @ X42)
% 0.43/0.61          | ~ (v1_relat_1 @ X42))),
% 0.43/0.61      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.43/0.61          | ~ (v1_relat_1 @ sk_B)
% 0.43/0.61          | ~ (v1_funct_1 @ sk_B)
% 0.43/0.61          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.43/0.61  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.43/0.61          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.43/0.61  thf('70', plain,
% 0.43/0.61      (![X15 : $i, X16 : $i]:
% 0.43/0.61         (((X15) = (k1_xboole_0))
% 0.43/0.61          | ((sk_C @ X16 @ X15) != (X16))
% 0.43/0.61          | ((X15) = (k1_tarski @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.43/0.61          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.43/0.61  thf('72', plain,
% 0.43/0.61      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.43/0.61        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['71'])).
% 0.43/0.61  thf('73', plain,
% 0.43/0.61      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('74', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.43/0.61  thf('75', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.43/0.61      inference('demod', [status(thm)], ['57', '74'])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_xboole_0) != (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_tarski @ X0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['48', '75'])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['76'])).
% 0.43/0.61  thf('78', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['76'])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_tarski @ X0) = (k1_tarski @ X1))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['77', '78'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.61          | ((k1_tarski @ X0) = (k1_tarski @ X1)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['79'])).
% 0.43/0.61  thf('81', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.61          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('82', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.43/0.62          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.62          | ((k11_relat_1 @ sk_B @ X1) != (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['80', '81'])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_tarski @ sk_A) = (k1_tarski @ X0))
% 0.43/0.62          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['76'])).
% 0.43/0.62  thf('84', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf('85', plain, ((v1_relat_1 @ sk_B)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('86', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf('87', plain,
% 0.43/0.62      (![X33 : $i, X34 : $i]:
% 0.43/0.62         (((k11_relat_1 @ X33 @ X34) = (k9_relat_1 @ X33 @ (k1_tarski @ X34)))
% 0.43/0.62          | ~ (v1_relat_1 @ X33))),
% 0.43/0.62      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.43/0.62          | ~ (v1_relat_1 @ X1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['86', '87'])).
% 0.43/0.62  thf('89', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k11_relat_1 @ sk_B @ X0)
% 0.43/0.62           = (k9_relat_1 @ sk_B @ (k2_tarski @ X0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['85', '88'])).
% 0.43/0.62  thf('90', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k11_relat_1 @ sk_B @ X0) = (k9_relat_1 @ sk_B @ (k1_tarski @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['84', '89'])).
% 0.43/0.62  thf('91', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k11_relat_1 @ sk_B @ X0) = (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.62          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['83', '90'])).
% 0.43/0.62  thf('92', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((k11_relat_1 @ sk_B @ X0) = (k9_relat_1 @ sk_B @ (k1_tarski @ X0)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['84', '89'])).
% 0.43/0.62  thf('93', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['57', '74'])).
% 0.43/0.62  thf('94', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.43/0.62          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.43/0.62  thf('95', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.43/0.62          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.43/0.62      inference('clc', [status(thm)], ['82', '94'])).
% 0.43/0.62  thf('96', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.43/0.62          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '95'])).
% 0.43/0.62  thf('97', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '96'])).
% 0.43/0.62  thf('98', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf('99', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['0', '9'])).
% 0.43/0.62  thf('100', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['98', '99'])).
% 0.43/0.62  thf('101', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.43/0.62      inference('sup+', [status(thm)], ['97', '100'])).
% 0.43/0.62  thf('102', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.43/0.62          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('103', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['10', '96'])).
% 0.43/0.62  thf('104', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.43/0.62          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['102', '103'])).
% 0.43/0.62  thf('105', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['101', '104'])).
% 0.43/0.62  thf('106', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['57', '74'])).
% 0.43/0.62  thf('107', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['105', '106'])).
% 0.43/0.62  thf('108', plain, ($false), inference('simplify', [status(thm)], ['107'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
