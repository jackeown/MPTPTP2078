%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BZ9jiQjqPi

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 210 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  847 (1902 expanded)
%              Number of equality atoms :  109 ( 228 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X25 @ X26 ) )
        = X26 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X25 @ X26 ) )
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('7',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('39',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X22 @ X19 ) @ ( sk_D @ X22 @ X19 ) ) @ X19 )
      | ( r2_hidden @ ( sk_C_2 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('45',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22
        = ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X22 @ X19 ) @ ( sk_D @ X22 @ X19 ) ) @ X19 )
      | ( r2_hidden @ ( sk_C_2 @ X22 @ X19 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('46',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('54',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','57'])).

thf('59',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('62',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('64',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('65',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('71',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('77',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','72','77'])).

thf('79',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('87',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['60','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BZ9jiQjqPi
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 168 iterations in 0.086s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(t15_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ?[C:$i]:
% 0.22/0.53           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.22/0.53             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.53             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         (((k1_relat_1 @ (sk_C_3 @ X25 @ X26)) = (X26))
% 0.22/0.53          | ((X26) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((v1_relat_1 @ (sk_C_3 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         ((v1_funct_1 @ (sk_C_3 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.53  thf(t3_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf(l1_zfmisc_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X10 : $i, X12 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.22/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.53          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (sk_C_3 @ X25 @ X26)) = (k1_tarski @ X25))
% 0.22/0.53          | ((X26) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.53  thf(t18_funct_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.53          ( ![C:$i]:
% 0.22/0.53            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.53                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.53             ( ![C:$i]:
% 0.22/0.53               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.53                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X27 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ X27))
% 0.22/0.53          | ~ (v1_funct_1 @ X27)
% 0.22/0.53          | ~ (v1_relat_1 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.22/0.53          | ((X1) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.22/0.53          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ sk_A @ X0)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.22/0.53          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.22/0.53          | ((X1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((X0) = (k1_xboole_0))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.53          | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ sk_A @ X1)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.53          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((X0) = (k1_xboole_0))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.53          | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '11'])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ sk_A @ X1)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((sk_B) != (X0))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | ((X0) = (k1_xboole_0))
% 0.22/0.53          | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X1 : $i]: ((r1_xboole_0 @ sk_A @ X1) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.53  thf(cc1_funct_1, axiom,
% 0.22/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.22/0.53  thf('16', plain, (![X24 : $i]: ((v1_funct_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.53  thf(cc1_relat_1, axiom,
% 0.22/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.22/0.53  thf('17', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.53  thf(t60_relat_1, axiom,
% 0.22/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X27 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ X27))
% 0.22/0.53          | ~ (v1_funct_1 @ X27)
% 0.22/0.53          | ~ (v1_relat_1 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.22/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.53        | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.53  thf('21', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('22', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.53        | ((sk_B) != (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53        | ((sk_B) != (k1_xboole_0))
% 0.22/0.53        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '23'])).
% 0.22/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.53  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      ((((sk_B) != (k1_xboole_0)) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B) != (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '26'])).
% 0.22/0.53  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.53  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf('30', plain, (![X1 : $i]: (r1_xboole_0 @ sk_A @ X1)),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['15', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.53          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.53          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['31', '34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.53  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '36'])).
% 0.22/0.53  thf(t4_boole, axiom,
% 0.22/0.53    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.53  thf(t83_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X6 : $i, X8 : $i]:
% 0.22/0.53         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.53  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf(d4_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X19 : $i, X22 : $i]:
% 0.22/0.53         (((X22) = (k1_relat_1 @ X19))
% 0.22/0.53          | (r2_hidden @ 
% 0.22/0.53             (k4_tarski @ (sk_C_2 @ X22 @ X19) @ (sk_D @ X22 @ X19)) @ X19)
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X22 @ X19) @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X19 : $i, X22 : $i]:
% 0.22/0.53         (((X22) = (k1_relat_1 @ X19))
% 0.22/0.53          | (r2_hidden @ 
% 0.22/0.53             (k4_tarski @ (sk_C_2 @ X22 @ X19) @ (sk_D @ X22 @ X19)) @ X19)
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X22 @ X19) @ X22))),
% 0.22/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('47', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.22/0.53          | ((X1) = (k1_relat_1 @ X0))
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.53          | ~ (r2_hidden @ 
% 0.22/0.53               (k4_tarski @ (sk_C_2 @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X2))),
% 0.22/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.22/0.53          | ((X1) = (k1_relat_1 @ X0))
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.22/0.53          | ((X1) = (k1_relat_1 @ X0))
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['44', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r1_xboole_0 @ X0 @ X0)
% 0.22/0.53          | ((X1) = (k1_relat_1 @ X0))
% 0.22/0.53          | (r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1))),
% 0.22/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.53          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['43', '49'])).
% 0.22/0.53  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('52', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((X0) = (k1_xboole_0))
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.53          | ~ (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((X0) = (k1_xboole_0))
% 0.22/0.53          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.22/0.53          | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '55'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.53  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '57'])).
% 0.22/0.53  thf('59', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('61', plain, (![X16 : $i]: ((v1_relat_1 @ X16) | ~ (v1_xboole_0 @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.22/0.53  thf('62', plain, (![X24 : $i]: ((v1_funct_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.22/0.53  thf('63', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('64', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('65', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['63', '64'])).
% 0.22/0.53  thf('66', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('67', plain,
% 0.22/0.53      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (![X27 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.22/0.53          | ((sk_B) != (k1_relat_1 @ X27))
% 0.22/0.53          | ~ (v1_funct_1 @ X27)
% 0.22/0.53          | ~ (v1_relat_1 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      (((~ (r1_tarski @ sk_B @ sk_A)
% 0.22/0.53         | ~ (v1_relat_1 @ sk_B)
% 0.22/0.53         | ~ (v1_funct_1 @ sk_B)
% 0.22/0.53         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.53  thf('70', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('71', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('72', plain,
% 0.22/0.53      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['70', '71'])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['73', '74'])).
% 0.22/0.53  thf('76', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('77', plain,
% 0.22/0.53      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      (((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ((sk_B) != (sk_B))))
% 0.22/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('demod', [status(thm)], ['69', '72', '77'])).
% 0.22/0.53  thf('79', plain,
% 0.22/0.53      (((~ (v1_funct_1 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.53  thf('80', plain,
% 0.22/0.53      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.53         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['62', '79'])).
% 0.22/0.53  thf('81', plain,
% 0.22/0.53      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.53  thf('83', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('84', plain, ((~ (v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('demod', [status(thm)], ['80', '83'])).
% 0.22/0.53  thf('85', plain, ((~ (v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['61', '84'])).
% 0.22/0.53  thf('86', plain, (((v1_xboole_0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('87', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.22/0.53  thf('88', plain, (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 0.22/0.53      inference('split', [status(esa)], ['59'])).
% 0.22/0.53  thf('89', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.22/0.53  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['60', '89'])).
% 0.22/0.53  thf('91', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['58', '90'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
