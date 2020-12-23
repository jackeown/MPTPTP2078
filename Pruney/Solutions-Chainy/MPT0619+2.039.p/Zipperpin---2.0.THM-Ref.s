%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJtbuAvuJj

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:25 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  154 (1947 expanded)
%              Number of leaves         :   24 ( 574 expanded)
%              Depth                    :   26
%              Number of atoms          : 1333 (19236 expanded)
%              Number of equality atoms :  154 (2508 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_3 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ X0 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = X1 )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( sk_C @ k1_xboole_0 @ X1 )
      = X1 ) ),
    inference('simplify_reflect-',[status(thm)],['6','12'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ( ( sk_C_3 @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X14 @ X15 ) @ X14 )
      | ( r2_hidden @ ( sk_D @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ ( k1_tarski @ sk_A ) )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_3 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('34',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('45',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( sk_C_2 @ sk_B )
      = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_C_2 @ sk_B )
    = ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('51',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('52',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ ( sk_D_1 @ X18 @ X15 ) @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('59',plain,
    ( ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_C_2 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['49','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_2 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_2 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ sk_B )
       != X0 )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k1_tarski @ ( sk_C_2 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ sk_B )
      = ( sk_C_2 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('70',plain,
    ( ( ( sk_D @ k1_xboole_0 @ sk_B )
      = sk_A )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('72',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ X7 )
        = X7 )
      | ~ ( r2_hidden @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('73',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('75',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_D @ k1_xboole_0 @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_3 @ X14 @ X15 )
        = ( k1_funct_1 @ X15 @ ( sk_D @ X14 @ X15 ) ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('78',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) )
    | ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('83',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('85',plain,
    ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','85'])).

thf('87',plain,
    ( ( sk_D_1 @ ( sk_C_2 @ sk_B ) @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('89',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('90',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X1 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    ! [X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X15 ) )
      | ( X18
        = ( k1_funct_1 @ X15 @ ( sk_D_1 @ X18 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_C_2 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C_2 @ X0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_2 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C_2 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( sk_C_2 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['87','98'])).

thf('100',plain,
    ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( sk_C_2 @ sk_B )
      = ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('106',plain,
    ( ( sk_C_2 @ sk_B )
    = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('107',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','106'])).

thf('108',plain,
    ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ sk_B )
    = ( sk_C_2 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['66','107'])).

thf('109',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ X14 @ X15 ) @ X14 )
      | ( ( sk_C_3 @ X14 @ X15 )
       != ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ( X14
        = ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( sk_C_2 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('112',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ sk_B )
    = ( sk_C_2 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['66','107'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_C_2 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C_2 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','115'])).

thf('117',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','106'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( sk_C_2 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( sk_C_2 @ sk_B )
     != ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','118'])).

thf('120',plain,
    ( ( sk_C_2 @ sk_B )
    = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['104','105'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( sk_D @ k1_xboole_0 @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('125',plain,
    ( ( ( sk_C_2 @ sk_B )
     != ( sk_C_2 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124'])).

thf('126',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['73','74'])).

thf('128',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wJtbuAvuJj
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 164 iterations in 0.145s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.44/0.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.44/0.65  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.44/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(d5_funct_1, axiom,
% 0.44/0.65    (![A:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.44/0.65       ( ![B:$i]:
% 0.44/0.65         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.44/0.65           ( ![C:$i]:
% 0.44/0.65             ( ( r2_hidden @ C @ B ) <=>
% 0.44/0.65               ( ?[D:$i]:
% 0.44/0.65                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.44/0.65                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X14 @ X15) @ X14)
% 0.44/0.65          | ((sk_C_3 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.44/0.65          | ((X14) = (k2_relat_1 @ X15))
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf(d1_tarski, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      (![X0 : $i, X4 : $i]:
% 0.44/0.65         (((X4) = (k1_tarski @ X0))
% 0.44/0.65          | ((sk_C @ X4 @ X0) = (X0))
% 0.44/0.65          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.65  thf(t46_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r2_hidden @ A @ B ) =>
% 0.44/0.65       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.44/0.65          | ~ (r2_hidden @ X8 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((sk_C @ X0 @ X1) = (X1))
% 0.44/0.65          | ((X0) = (k1_tarski @ X1))
% 0.44/0.65          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ X1)) @ X0) = (X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.65  thf(t49_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((X0) != (k1_xboole_0))
% 0.44/0.65          | ((X0) = (k1_tarski @ X1))
% 0.44/0.65          | ((sk_C @ X0 @ X1) = (X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X1 : $i]:
% 0.44/0.65         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 0.44/0.65          | ((k1_xboole_0) = (k1_tarski @ X1)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.65  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.44/0.65          | ~ (r2_hidden @ X8 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.44/0.65           = (k1_tarski @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.44/0.65  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.65  thf('13', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X0 : $i, X4 : $i]:
% 0.44/0.65         (((X4) = (k1_tarski @ X0))
% 0.44/0.65          | ((sk_C @ X4 @ X0) != (X0))
% 0.44/0.65          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.44/0.65          | ((sk_C @ k1_xboole_0 @ X0) != (X0))
% 0.44/0.65          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.65  thf('16', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.44/0.65          | ((X0) != (X0))
% 0.44/0.65          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.65  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.65  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X0)
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 0.44/0.65          | ((sk_C_3 @ k1_xboole_0 @ X0)
% 0.44/0.65              = (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0))))),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '20'])).
% 0.44/0.65  thf(t14_funct_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.65       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.44/0.65         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i]:
% 0.44/0.65        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.65          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.44/0.65            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.44/0.65  thf('22', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X14 @ X15) @ X14)
% 0.44/0.65          | (r2_hidden @ (sk_D @ X14 @ X15) @ (k1_relat_1 @ X15))
% 0.44/0.65          | ((X14) = (k2_relat_1 @ X15))
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65          | ((X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | (r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('27', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_D @ X0 @ sk_B) @ (k1_tarski @ sk_A))
% 0.44/0.65          | ((X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | (r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.65  thf('28', plain,
% 0.44/0.65      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X0 : $i, X3 : $i]:
% 0.44/0.65         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.65  thf('30', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0)
% 0.44/0.65          | ((X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['27', '29'])).
% 0.44/0.65  thf('31', plain,
% 0.44/0.65      (![X0 : $i, X3 : $i]:
% 0.44/0.65         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.65  thf('32', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.65  thf('33', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X14 @ X15) @ X14)
% 0.44/0.65          | ((sk_C_3 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.44/0.65          | ((X14) = (k2_relat_1 @ X15))
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('34', plain,
% 0.44/0.65      (![X0 : $i, X3 : $i]:
% 0.44/0.65         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.65  thf('35', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X1)
% 0.44/0.65          | ~ (v1_funct_1 @ X1)
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ X1)
% 0.44/0.65              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.65  thf('36', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65          | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup+', [status(thm)], ['32', '35'])).
% 0.44/0.65  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.65  thf('38', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t18_relat_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( v1_relat_1 @ B ) =>
% 0.44/0.65       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.44/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.44/0.65  thf('39', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_2 @ X11) @ (k2_relat_1 @ X11))
% 0.44/0.65          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.44/0.65          | ~ (v1_relat_1 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.44/0.65  thf('40', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.65  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('42', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['40', '41'])).
% 0.44/0.65  thf('43', plain, ((r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['37', '42'])).
% 0.44/0.65  thf('44', plain,
% 0.44/0.65      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.44/0.65         (((X17) != (k2_relat_1 @ X15))
% 0.44/0.65          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15)))
% 0.44/0.65          | ~ (r2_hidden @ X18 @ X17)
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('45', plain,
% 0.44/0.65      (![X15 : $i, X18 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X15)
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.44/0.65          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.65  thf('46', plain,
% 0.44/0.65      ((((sk_C_2 @ sk_B)
% 0.44/0.65          = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B)))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['43', '45'])).
% 0.44/0.65  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('49', plain,
% 0.44/0.65      (((sk_C_2 @ sk_B)
% 0.44/0.65         = (k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.44/0.65  thf('50', plain, ((r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['37', '42'])).
% 0.44/0.65  thf('51', plain,
% 0.44/0.65      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.44/0.65         (((X17) != (k2_relat_1 @ X15))
% 0.44/0.65          | (r2_hidden @ (sk_D_1 @ X18 @ X15) @ (k1_relat_1 @ X15))
% 0.44/0.65          | ~ (r2_hidden @ X18 @ X17)
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('52', plain,
% 0.44/0.65      (![X15 : $i, X18 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X15)
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.44/0.65          | (r2_hidden @ (sk_D_1 @ X18 @ X15) @ (k1_relat_1 @ X15)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['51'])).
% 0.44/0.65  thf('53', plain,
% 0.44/0.65      (((r2_hidden @ (sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['50', '52'])).
% 0.44/0.65  thf('54', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('57', plain,
% 0.44/0.65      ((r2_hidden @ (sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B) @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.44/0.65  thf('58', plain,
% 0.44/0.65      (![X0 : $i, X3 : $i]:
% 0.44/0.65         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['28'])).
% 0.44/0.65  thf('59', plain, (((sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B) = (sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.65  thf('60', plain, (((sk_C_2 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.44/0.65      inference('demod', [status(thm)], ['49', '59'])).
% 0.44/0.65  thf('61', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('63', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_2 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['36', '60', '61', '62'])).
% 0.44/0.65  thf('64', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_2 @ sk_B)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.44/0.65  thf('65', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_C_2 @ sk_B) != (X0))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.44/0.65          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('eq_fact', [status(thm)], ['64'])).
% 0.44/0.65  thf('66', plain,
% 0.44/0.65      ((((k1_tarski @ (sk_C_2 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.44/0.65        | ((sk_C_3 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ sk_B) = (sk_C_2 @ sk_B)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['65'])).
% 0.44/0.65  thf('67', plain,
% 0.44/0.65      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('68', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0)
% 0.44/0.65          | ((X0) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['27', '29'])).
% 0.44/0.65  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('70', plain,
% 0.44/0.65      ((((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))
% 0.44/0.65        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.44/0.65  thf('71', plain, ((r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['37', '42'])).
% 0.44/0.65  thf('72', plain,
% 0.44/0.65      (![X7 : $i, X8 : $i]:
% 0.44/0.65         (((k2_xboole_0 @ (k1_tarski @ X8) @ X7) = (X7))
% 0.44/0.65          | ~ (r2_hidden @ X8 @ X7))),
% 0.44/0.65      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.44/0.65  thf('73', plain,
% 0.44/0.65      (((k2_xboole_0 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 0.44/0.65         = (k2_relat_1 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.44/0.65  thf('74', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i]:
% 0.44/0.65         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.44/0.65  thf('75', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.65  thf('76', plain, (((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.44/0.65  thf('77', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_3 @ X14 @ X15) @ X14)
% 0.44/0.65          | ((sk_C_3 @ X14 @ X15) = (k1_funct_1 @ X15 @ (sk_D @ X14 @ X15)))
% 0.44/0.65          | ((X14) = (k2_relat_1 @ X15))
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('78', plain,
% 0.44/0.65      ((((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.44/0.65        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65        | ((k1_xboole_0) = (k2_relat_1 @ sk_B))
% 0.44/0.65        | (r2_hidden @ (sk_C_3 @ k1_xboole_0 @ sk_B) @ k1_xboole_0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['76', '77'])).
% 0.44/0.65  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('81', plain,
% 0.44/0.65      ((((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.44/0.65        | ((k1_xboole_0) = (k2_relat_1 @ sk_B))
% 0.44/0.65        | (r2_hidden @ (sk_C_3 @ k1_xboole_0 @ sk_B) @ k1_xboole_0))),
% 0.44/0.65      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.44/0.65  thf('82', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.65  thf('83', plain,
% 0.44/0.65      ((((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.44/0.65        | (r2_hidden @ (sk_C_3 @ k1_xboole_0 @ sk_B) @ k1_xboole_0))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.44/0.65  thf('84', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('85', plain,
% 0.44/0.65      (((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.44/0.65      inference('clc', [status(thm)], ['83', '84'])).
% 0.44/0.65  thf('86', plain,
% 0.44/0.65      (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['67', '85'])).
% 0.44/0.65  thf('87', plain, (((sk_D_1 @ (sk_C_2 @ sk_B) @ sk_B) = (sk_A))),
% 0.44/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.44/0.65  thf('88', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.65  thf(t41_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.65          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.44/0.65  thf('89', plain,
% 0.44/0.65      (![X5 : $i, X6 : $i]:
% 0.44/0.65         (((X5) = (k1_xboole_0))
% 0.44/0.65          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.44/0.65          | ((X5) = (k1_tarski @ X6)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.44/0.65  thf('90', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_2 @ X11) @ (k2_relat_1 @ X11))
% 0.44/0.65          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.44/0.65          | ~ (v1_relat_1 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.44/0.65  thf('91', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 0.44/0.65          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X0)
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ X0) @ (k2_relat_1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.65  thf('92', plain,
% 0.44/0.65      (![X11 : $i, X12 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_2 @ X11) @ (k2_relat_1 @ X11))
% 0.44/0.65          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.44/0.65          | ~ (v1_relat_1 @ X11))),
% 0.44/0.65      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.44/0.65  thf('93', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ X1) @ (k2_relat_1 @ X1))
% 0.44/0.65          | ~ (v1_relat_1 @ X1)
% 0.44/0.65          | ((k1_relat_1 @ X1) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X1)
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ X1) @ (k2_relat_1 @ X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['91', '92'])).
% 0.44/0.65  thf('94', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X1) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X1)
% 0.44/0.65          | (r2_hidden @ (sk_C_2 @ X1) @ (k2_relat_1 @ X1))
% 0.44/0.65          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['93'])).
% 0.44/0.65  thf('95', plain,
% 0.44/0.65      (![X1 : $i]:
% 0.44/0.65         ((r2_hidden @ (sk_C_2 @ X1) @ (k2_relat_1 @ X1))
% 0.44/0.65          | ~ (v1_relat_1 @ X1)
% 0.44/0.65          | ((k1_relat_1 @ X1) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['88', '94'])).
% 0.44/0.65  thf('96', plain,
% 0.44/0.65      (![X15 : $i, X18 : $i]:
% 0.44/0.65         (~ (v1_relat_1 @ X15)
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X15))
% 0.44/0.65          | ((X18) = (k1_funct_1 @ X15 @ (sk_D_1 @ X18 @ X15))))),
% 0.44/0.65      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.65  thf('97', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_relat_1 @ X0)
% 0.44/0.65          | ((sk_C_2 @ X0) = (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_C_2 @ X0) @ X0)))
% 0.44/0.65          | ~ (v1_funct_1 @ X0)
% 0.44/0.65          | ~ (v1_relat_1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['95', '96'])).
% 0.44/0.65  thf('98', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (v1_funct_1 @ X0)
% 0.44/0.65          | ((sk_C_2 @ X0) = (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_C_2 @ X0) @ X0)))
% 0.44/0.65          | ~ (v1_relat_1 @ X0)
% 0.44/0.65          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.44/0.65      inference('simplify', [status(thm)], ['97'])).
% 0.44/0.65  thf('99', plain,
% 0.44/0.65      ((((sk_C_2 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.44/0.65        | ((k1_relat_1 @ sk_B) = (k1_xboole_0))
% 0.44/0.65        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_B))),
% 0.44/0.65      inference('sup+', [status(thm)], ['87', '98'])).
% 0.44/0.65  thf('100', plain,
% 0.44/0.65      (((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.44/0.65      inference('clc', [status(thm)], ['83', '84'])).
% 0.44/0.65  thf('101', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('102', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('103', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('104', plain,
% 0.44/0.65      ((((sk_C_2 @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.44/0.65        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.44/0.65      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.44/0.65  thf('105', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.65  thf('106', plain, (((sk_C_2 @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 0.44/0.65  thf('107', plain, (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_2 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['86', '106'])).
% 0.44/0.65  thf('108', plain,
% 0.44/0.65      (((sk_C_3 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ sk_B) = (sk_C_2 @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['66', '107'])).
% 0.44/0.65  thf('109', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         (~ (r2_hidden @ (sk_C_3 @ X14 @ X15) @ X14)
% 0.44/0.65          | ((sk_C_3 @ X14 @ X15) != (k1_funct_1 @ X15 @ X16))
% 0.44/0.65          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.44/0.65          | ((X14) = (k2_relat_1 @ X15))
% 0.44/0.65          | ~ (v1_funct_1 @ X15)
% 0.44/0.65          | ~ (v1_relat_1 @ X15))),
% 0.44/0.65      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.44/0.65  thf('110', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ (sk_C_2 @ sk_B) @ (k1_tarski @ (sk_C_2 @ sk_B)))
% 0.44/0.65          | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65          | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65          | ((k1_tarski @ (sk_C_2 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.44/0.65          | ((sk_C_3 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ sk_B)
% 0.44/0.65              != (k1_funct_1 @ sk_B @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['108', '109'])).
% 0.44/0.65  thf('111', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.65  thf('112', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('114', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('115', plain,
% 0.44/0.65      (((sk_C_3 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ sk_B) = (sk_C_2 @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['66', '107'])).
% 0.44/0.65  thf('116', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((k1_tarski @ (sk_C_2 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.65          | ((sk_C_2 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['110', '111', '112', '113', '114', '115'])).
% 0.44/0.65  thf('117', plain, (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_2 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['86', '106'])).
% 0.44/0.65  thf('118', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.65          | ((sk_C_2 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['116', '117'])).
% 0.44/0.65  thf('119', plain,
% 0.44/0.65      ((((sk_C_2 @ sk_B) != (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.44/0.65        | ((k1_xboole_0) = (k2_relat_1 @ sk_B))
% 0.44/0.65        | ~ (v1_funct_1 @ sk_B)
% 0.44/0.65        | ~ (v1_relat_1 @ sk_B)
% 0.44/0.65        | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['21', '118'])).
% 0.44/0.65  thf('120', plain, (((sk_C_2 @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['104', '105'])).
% 0.44/0.65  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('122', plain, ((v1_relat_1 @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('123', plain, (((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.44/0.65  thf('124', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.65  thf('125', plain,
% 0.44/0.65      ((((sk_C_2 @ sk_B) != (sk_C_2 @ sk_B))
% 0.44/0.65        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)],
% 0.44/0.65                ['119', '120', '121', '122', '123', '124'])).
% 0.44/0.65  thf('126', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.44/0.65      inference('simplify', [status(thm)], ['125'])).
% 0.44/0.65  thf('127', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.65  thf('128', plain, ($false),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
