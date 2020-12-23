%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GkuVMUVg2A

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 224 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  865 (2260 expanded)
%              Number of equality atoms :  108 ( 273 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k11_relat_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X19 @ X18 ) @ X18 )
      | ( X18
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X26 ) @ ( k1_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X26: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k2_relat_1 @ X26 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X26 ) @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ( ( k11_relat_1 @ X23 @ X24 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('41',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k11_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ X20 @ ( k1_tarski @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('45',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k11_relat_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) @ sk_B )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X19 @ X18 ) @ X18 )
      | ( X18
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('55',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( X28
       != ( k2_relat_1 @ X26 ) )
      | ( X29
        = ( k1_funct_1 @ X26 @ ( sk_D_1 @ X29 @ X26 ) ) )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('56',plain,(
    ! [X26: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( r2_hidden @ X29 @ ( k2_relat_1 @ X26 ) )
      | ( X29
        = ( k1_funct_1 @ X26 @ ( sk_D_1 @ X29 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','47'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( sk_C @ X19 @ X18 )
       != X19 )
      | ( X18
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','47'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GkuVMUVg2A
% 0.14/0.36  % Computer   : n018.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:33:12 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 259 iterations in 0.187s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.66  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.46/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(d1_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, axiom,
% 0.46/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.46/0.66          | ((X1) = (X2))
% 0.46/0.66          | ((X1) = (X3))
% 0.46/0.66          | ((X1) = (X4)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t14_funct_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.66         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_1, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i]:
% 0.46/0.66        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.46/0.66            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.46/0.66  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf(t205_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ B ) =>
% 0.46/0.66       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.46/0.66         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (((k11_relat_1 @ X23 @ X24) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.46/0.66          | ~ (v1_relat_1 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.66  thf(t69_enumset1, axiom,
% 0.46/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.66  thf('6', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf(t70_enumset1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.66  thf(zf_stmt_3, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.66       ( ![E:$i]:
% 0.46/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X10 @ X9)
% 0.46/0.66          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.46/0.66          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.46/0.66         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.46/0.66          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['7', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['6', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (sk_A))
% 0.46/0.66          | ((X0) = (sk_A))
% 0.46/0.66          | ((X0) = (sk_A))
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k11_relat_1 @ sk_B @ X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.66  thf('15', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf(l44_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.66          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (((X18) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X19 @ X18) @ X18)
% 0.46/0.66          | ((X18) = (k1_tarski @ X19)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.46/0.66  thf(d5_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( r2_hidden @ C @ B ) <=>
% 0.46/0.66               ( ?[D:$i]:
% 0.46/0.66                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.46/0.66                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.66         (((X28) != (k2_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ X29 @ X26) @ (k1_relat_1 @ X26))
% 0.46/0.66          | ~ (r2_hidden @ X29 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X26 : $i, X29 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (r2_hidden @ X29 @ (k2_relat_1 @ X26))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ X29 @ X26) @ (k1_relat_1 @ X26)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.46/0.66          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.46/0.66             (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '18'])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.46/0.66           (k1_tarski @ sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['15', '19'])).
% 0.46/0.66  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.46/0.66           (k1_tarski @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.66         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.46/0.66          | (r2_hidden @ X5 @ X9)
% 0.46/0.66          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.66         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.46/0.66          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.46/0.66      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.46/0.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.46/0.66      inference('sup+', [status(thm)], ['25', '27'])).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.46/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '30'])).
% 0.46/0.66  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['24', '31'])).
% 0.46/0.66  thf('33', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.46/0.66          | ((k11_relat_1 @ X23 @ X24) != (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['32', '37'])).
% 0.46/0.66  thf('39', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf(t146_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X22 : $i]:
% 0.46/0.66         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 0.46/0.66          | ~ (v1_relat_1 @ X22))),
% 0.46/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf(d16_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i]:
% 0.46/0.66         (((k11_relat_1 @ X20 @ X21) = (k9_relat_1 @ X20 @ (k1_tarski @ X21)))
% 0.46/0.66          | ~ (v1_relat_1 @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('47', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.66  thf('48', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) @ 
% 0.46/0.66           (k1_tarski @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['23', '48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k11_relat_1 @ sk_B @ 
% 0.46/0.66              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B))
% 0.46/0.66              != (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.66          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_B)) @ sk_B) = (sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (((X18) = (k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X19 @ X18) @ X18)
% 0.46/0.66          | ((X18) = (k1_tarski @ X19)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.66         (((X28) != (k2_relat_1 @ X26))
% 0.46/0.66          | ((X29) = (k1_funct_1 @ X26 @ (sk_D_1 @ X29 @ X26)))
% 0.46/0.66          | ~ (r2_hidden @ X29 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X26))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X26 : $i, X29 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X26)
% 0.46/0.66          | ~ (v1_funct_1 @ X26)
% 0.46/0.66          | ~ (r2_hidden @ X29 @ (k2_relat_1 @ X26))
% 0.46/0.66          | ((X29) = (k1_funct_1 @ X26 @ (sk_D_1 @ X29 @ X26))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 0.46/0.66          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.46/0.66              = (k1_funct_1 @ X0 @ 
% 0.46/0.66                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['54', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ sk_B)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['53', '57'])).
% 0.46/0.66  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['61'])).
% 0.46/0.66  thf('63', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '47'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (((X18) = (k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X19 @ X18) != (X19))
% 0.46/0.66          | ((X18) = (k1_tarski @ X19)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.46/0.66          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.46/0.66        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.66  thf('69', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '47'])).
% 0.46/0.66  thf('70', plain, ($false),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['67', '68', '69'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
