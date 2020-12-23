%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exdiEReFX2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 (1191 expanded)
%              Number of leaves         :   21 ( 356 expanded)
%              Depth                    :   28
%              Number of atoms          :  955 (11325 expanded)
%              Number of equality atoms :  120 (1590 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X13 @ X14 ) @ X13 )
      | ( ( sk_C_3 @ X13 @ X14 )
        = ( k1_funct_1 @ X14 @ ( sk_D @ X13 @ X14 ) ) )
      | ( X13
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X5 )
        = X5 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

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
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X5 )
        = X5 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

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

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X13 @ X14 ) @ X13 )
      | ( r2_hidden @ ( sk_D @ X13 @ X14 ) @ ( k1_relat_1 @ X14 ) )
      | ( X13
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

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

thf('23',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

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
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X13 @ X14 ) @ X13 )
      | ( ( sk_C_3 @ X13 @ X14 )
        = ( k1_funct_1 @ X14 @ ( sk_D @ X13 @ X14 ) ) )
      | ( X13
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ sk_A ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ X0 @ sk_B ) @ X0 )
      | ( ( sk_D @ X0 @ sk_B )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('37',plain,
    ( ( ( sk_D @ k1_xboole_0 @ sk_B )
      = sk_A )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X11 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t18_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X5 )
        = X5 )
      | ~ ( r2_hidden @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('46',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_2 @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('48',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_D @ k1_xboole_0 @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ( ( sk_C_3 @ k1_xboole_0 @ X0 )
        = ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('51',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
      = ( k1_funct_1 @ sk_B @ sk_A ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('56',plain,
    ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
       != X0 )
      | ( ( sk_C_3 @ ( k1_tarski @ X0 ) @ sk_B )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,
    ( ( ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) @ sk_B )
      = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) @ sk_B )
    = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ X13 @ X14 ) @ X13 )
      | ( ( sk_C_3 @ X13 @ X14 )
       != ( k1_funct_1 @ X14 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X14 ) )
      | ( X13
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) @ ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C_3 @ ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) @ sk_B )
    = ( sk_C_3 @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
        = ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( sk_C_3 @ k1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
       != ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
     != ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_D @ k1_xboole_0 @ sk_B )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','48'])).

thf('83',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('84',plain,
    ( ( ( sk_C_3 @ k1_xboole_0 @ sk_B )
     != ( sk_C_3 @ k1_xboole_0 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exdiEReFX2
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 107 iterations in 0.082s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(d5_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.53               ( ?[D:$i]:
% 0.20/0.53                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.53                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_3 @ X13 @ X14) @ X13)
% 0.20/0.53          | ((sk_C_3 @ X13 @ X14) = (k1_funct_1 @ X14 @ (sk_D @ X13 @ X14)))
% 0.20/0.53          | ((X13) = (k2_relat_1 @ X14))
% 0.20/0.53          | ~ (v1_funct_1 @ X14)
% 0.20/0.53          | ~ (v1_relat_1 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X0 : $i, X4 : $i]:
% 0.20/0.53         (((X4) = (k1_tarski @ X0))
% 0.20/0.53          | ((sk_C @ X4 @ X0) = (X0))
% 0.20/0.53          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf(l22_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ (k1_tarski @ X6) @ X5) = (X5))
% 0.20/0.53          | ~ (r2_hidden @ X6 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((sk_C @ X0 @ X1) = (X1))
% 0.20/0.53          | ((X0) = (k1_tarski @ X1))
% 0.20/0.53          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ X1)) @ X0) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(t49_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) != (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_tarski @ X1))
% 0.20/0.53          | ((sk_C @ X0 @ X1) = (X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X1 : $i]:
% 0.20/0.53         (((sk_C @ k1_xboole_0 @ X1) = (X1))
% 0.20/0.53          | ((k1_xboole_0) = (k1_tarski @ X1)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ (k1_tarski @ X6) @ X5) = (X5))
% 0.20/0.53          | ~ (r2_hidden @ X6 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.20/0.53           = (k1_tarski @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.53  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X4 : $i]:
% 0.20/0.53         (((X4) = (k1_tarski @ X0))
% 0.20/0.53          | ((sk_C @ X4 @ X0) != (X0))
% 0.20/0.53          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.53          | ((sk_C @ k1_xboole_0 @ X0) != (X0))
% 0.20/0.53          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, (![X1 : $i]: ((sk_C @ k1_xboole_0 @ X1) = (X1))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['6', '12'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.53          | ((X0) != (X0))
% 0.20/0.53          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('19', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 0.20/0.53          | ((sk_C_3 @ k1_xboole_0 @ X0)
% 0.20/0.53              = (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_3 @ X13 @ X14) @ X13)
% 0.20/0.53          | (r2_hidden @ (sk_D @ X13 @ X14) @ (k1_relat_1 @ X14))
% 0.20/0.53          | ((X13) = (k2_relat_1 @ X14))
% 0.20/0.53          | ~ (v1_funct_1 @ X14)
% 0.20/0.53          | ~ (v1_relat_1 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.53  thf(t14_funct_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.53         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.53            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.53  thf('23', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X3 : $i]:
% 0.20/0.53         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)) | ((X0) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ sk_B)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53          | ((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | (r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0)
% 0.20/0.53          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.53  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | (r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0)
% 0.20/0.53          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X3 : $i]:
% 0.20/0.53         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_D @ (k1_tarski @ X0) @ sk_B) = (sk_A))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_3 @ X13 @ X14) @ X13)
% 0.20/0.53          | ((sk_C_3 @ X13 @ X14) = (k1_funct_1 @ X14 @ (sk_D @ X13 @ X14)))
% 0.20/0.53          | ((X13) = (k2_relat_1 @ X14))
% 0.20/0.53          | ~ (v1_funct_1 @ X14)
% 0.20/0.53          | ~ (v1_relat_1 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | (r2_hidden @ (sk_C_3 @ (k1_tarski @ X0) @ sk_B) @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | (r2_hidden @ (sk_C_3 @ X0 @ sk_B) @ X0)
% 0.20/0.53          | ((sk_D @ X0 @ sk_B) = (sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.53  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))
% 0.20/0.53        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('40', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf(t18_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ~( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_2 @ X11) @ (k2_relat_1 @ X11))
% 0.20/0.53          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.20/0.53          | ~ (v1_relat_1 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [t18_relat_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((r2_hidden @ (sk_C_2 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ (k1_tarski @ X6) @ X5) = (X5))
% 0.20/0.53          | ~ (r2_hidden @ X6 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((k2_xboole_0 @ (k1_tarski @ (sk_C_2 @ sk_B)) @ (k2_relat_1 @ sk_B))
% 0.20/0.53         = (k2_relat_1 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.53  thf('48', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, (((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['37', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 0.20/0.53          | ((sk_C_3 @ k1_xboole_0 @ X0)
% 0.20/0.53              = (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '20'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.20/0.53        | ((k1_xboole_0) = (k2_relat_1 @ sk_B))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))
% 0.20/0.53        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.20/0.53  thf('55', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('57', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('58', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | (r2_hidden @ (sk_C_3 @ (k1_tarski @ X0) @ sk_B) @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '56', '57', '58'])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_3 @ (k1_tarski @ X0) @ sk_B) @ (k1_tarski @ X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X3 : $i]:
% 0.20/0.53         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ X0) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((sk_C_3 @ k1_xboole_0 @ sk_B) != (X0))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ X0) @ sk_B) = (X0))
% 0.20/0.53          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((((k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.20/0.53        | ((sk_C_3 @ (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) @ sk_B)
% 0.20/0.53            = (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((sk_C_3 @ k1_xboole_0 @ sk_B) = (k1_funct_1 @ sk_B @ sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((sk_C_3 @ (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) @ sk_B)
% 0.20/0.53         = (sk_C_3 @ k1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (sk_C_3 @ X13 @ X14) @ X13)
% 0.20/0.53          | ((sk_C_3 @ X13 @ X14) != (k1_funct_1 @ X14 @ X15))
% 0.20/0.53          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X14))
% 0.20/0.53          | ((X13) = (k2_relat_1 @ X14))
% 0.20/0.53          | ~ (v1_funct_1 @ X14)
% 0.20/0.53          | ~ (v1_relat_1 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (sk_C_3 @ k1_xboole_0 @ sk_B) @ 
% 0.20/0.53             (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)))
% 0.20/0.53          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53          | ((k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) @ sk_B)
% 0.20/0.53              != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.53  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (((sk_C_3 @ (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) @ sk_B)
% 0.20/0.53         = (sk_C_3 @ k1_xboole_0 @ sk_B))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ k1_xboole_0 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.20/0.53  thf('77', plain,
% 0.20/0.53      (((k2_relat_1 @ sk_B) != (k1_tarski @ (sk_C_3 @ k1_xboole_0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.53          | ((sk_C_3 @ k1_xboole_0 @ sk_B) != (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((((sk_C_3 @ k1_xboole_0 @ sk_B) != (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.20/0.53        | ((k1_xboole_0) = (k2_relat_1 @ sk_B))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53        | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B) @ (k1_relat_1 @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '78'])).
% 0.20/0.53  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('82', plain, (((sk_D @ k1_xboole_0 @ sk_B) = (sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['37', '48'])).
% 0.20/0.53  thf('83', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      ((((sk_C_3 @ k1_xboole_0 @ sk_B) != (sk_C_3 @ k1_xboole_0 @ sk_B))
% 0.20/0.53        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.20/0.53  thf('85', plain, (((k1_xboole_0) = (k2_relat_1 @ sk_B))),
% 0.20/0.53      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.53  thf('86', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('87', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
