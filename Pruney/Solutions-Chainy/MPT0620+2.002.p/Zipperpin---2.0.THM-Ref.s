%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J6XbUs3qXO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:27 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 192 expanded)
%              Number of leaves         :   20 (  70 expanded)
%              Depth                    :   24
%              Number of atoms          : 1110 (2586 expanded)
%              Number of equality atoms :  123 ( 299 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X2 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X6 @ X5 ) @ X5 )
      | ( X5
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

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

thf('5',plain,(
    ! [X8: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( X12
       != ( k1_funct_1 @ X8 @ X13 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_tarski @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_3 @ X2 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X2 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k1_tarski @ X2 ) )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X8: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_C_3 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X2 @ X0 ) @ ( sk_D_1 @ X1 @ ( sk_C_3 @ X1 @ X0 ) ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_2 @ X7 @ X8 )
        = ( k1_funct_1 @ X8 @ ( sk_D @ X7 @ X8 ) ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X8 ) @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('33',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X3 @ X0 ) @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X2 )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( sk_C_3 @ X2 @ X1 ) )
        = X2 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X2 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['45'])).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X2 @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X2 @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_3 @ X2 @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X2 ) @ ( sk_C_3 @ X2 @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X7 @ X8 ) @ X7 )
      | ( ( sk_C_2 @ X7 @ X8 )
       != ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ( X7
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( sk_C_3 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( sk_C_3 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) @ ( sk_C_3 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_funct_1 @ ( sk_C_3 @ X0 @ X2 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) )
      | ( X0
       != ( k1_funct_1 @ ( sk_C_3 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( sk_C_3 @ X2 @ X1 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X2 @ ( sk_C_3 @ X2 @ X1 ) ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(t15_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
          ? [C: $i] :
            ( ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) )
            & ( ( k1_relat_1 @ C )
              = A )
            & ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_funct_1])).

thf('63',plain,(
    ! [X17: $i] :
      ( ( ( k2_relat_1 @ X17 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X17 )
       != sk_A )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( X1 = k1_xboole_0 )
      | ( X1 != sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(eq_res,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J6XbUs3qXO
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/1.00  % Solved by: fo/fo7.sh
% 0.74/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/1.00  % done 342 iterations in 0.547s
% 0.74/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/1.00  % SZS output start Refutation
% 0.74/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.74/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.74/1.00  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.74/1.00  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.74/1.00  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.74/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.74/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.74/1.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.74/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/1.00  thf(t41_zfmisc_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.74/1.00          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.74/1.00  thf('0', plain,
% 0.74/1.00      (![X5 : $i, X6 : $i]:
% 0.74/1.00         (((X5) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.74/1.00          | ((X5) = (k1_tarski @ X6)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.74/1.00  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ?[C:$i]:
% 0.74/1.00       ( ( ![D:$i]:
% 0.74/1.00           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.74/1.00         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.74/1.00         ( v1_relat_1 @ C ) ) ))).
% 0.74/1.00  thf('1', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/1.00         (((k1_funct_1 @ (sk_C_3 @ X14 @ X15) @ X16) = (X14))
% 0.74/1.00          | ~ (r2_hidden @ X16 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('2', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) = (k1_tarski @ X1))
% 0.74/1.00          | ((X0) = (k1_xboole_0))
% 0.74/1.00          | ((k1_funct_1 @ (sk_C_3 @ X2 @ X0) @ (sk_C_1 @ X1 @ X0)) = (X2)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.74/1.00  thf('3', plain,
% 0.74/1.00      (![X5 : $i, X6 : $i]:
% 0.74/1.00         (((X5) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ (sk_C_1 @ X6 @ X5) @ X5)
% 0.74/1.00          | ((X5) = (k1_tarski @ X6)))),
% 0.74/1.00      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.74/1.00  thf('4', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_3 @ X14 @ X15)) = (X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf(d5_funct_1, axiom,
% 0.74/1.00    (![A:$i]:
% 0.74/1.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.00       ( ![B:$i]:
% 0.74/1.00         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.74/1.00           ( ![C:$i]:
% 0.74/1.00             ( ( r2_hidden @ C @ B ) <=>
% 0.74/1.00               ( ?[D:$i]:
% 0.74/1.00                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.74/1.00                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.74/1.00  thf('5', plain,
% 0.74/1.00      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.74/1.00         (((X10) != (k2_relat_1 @ X8))
% 0.74/1.00          | (r2_hidden @ X12 @ X10)
% 0.74/1.00          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.74/1.00          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (v1_relat_1 @ X8))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/1.00  thf('6', plain,
% 0.74/1.00      (![X8 : $i, X13 : $i]:
% 0.74/1.00         (~ (v1_relat_1 @ X8)
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 0.74/1.00          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['5'])).
% 0.74/1.00  thf('7', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X2 @ X0)
% 0.74/1.00          | (r2_hidden @ (k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ X2) @ 
% 0.74/1.00             (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['4', '6'])).
% 0.74/1.00  thf('8', plain, (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('9', plain, (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('10', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X2 @ X0)
% 0.74/1.00          | (r2_hidden @ (k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ X2) @ 
% 0.74/1.00             (k2_relat_1 @ (sk_C_3 @ X1 @ X0))))),
% 0.74/1.00      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.74/1.00  thf('11', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) = (k1_tarski @ X1))
% 0.74/1.00          | ((X0) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ 
% 0.74/1.00             (k1_funct_1 @ (sk_C_3 @ X2 @ X0) @ (sk_C_1 @ X1 @ X0)) @ 
% 0.74/1.00             (k2_relat_1 @ (sk_C_3 @ X2 @ X0))))),
% 0.74/1.00      inference('sup-', [status(thm)], ['3', '10'])).
% 0.74/1.00  thf('12', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         ((r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | ((X1) = (k1_tarski @ X2))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | ((X1) = (k1_tarski @ X2)))),
% 0.74/1.00      inference('sup+', [status(thm)], ['2', '11'])).
% 0.74/1.00  thf('13', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X1) = (k1_tarski @ X2))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.74/1.00      inference('simplify', [status(thm)], ['12'])).
% 0.74/1.00  thf(d1_tarski, axiom,
% 0.74/1.00    (![A:$i,B:$i]:
% 0.74/1.00     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.74/1.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.74/1.00  thf('14', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d1_tarski])).
% 0.74/1.00  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.74/1.00      inference('simplify', [status(thm)], ['14'])).
% 0.74/1.00  thf('16', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         ((r2_hidden @ X1 @ X0)
% 0.74/1.00          | (r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_3 @ X2 @ X0)))
% 0.74/1.00          | ((X0) = (k1_xboole_0)))),
% 0.74/1.00      inference('sup+', [status(thm)], ['13', '15'])).
% 0.74/1.00  thf('17', plain,
% 0.74/1.00      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.74/1.00         (((X10) != (k2_relat_1 @ X8))
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8))
% 0.74/1.00          | ~ (r2_hidden @ X11 @ X10)
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (v1_relat_1 @ X8))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/1.00  thf('18', plain,
% 0.74/1.00      (![X8 : $i, X11 : $i]:
% 0.74/1.00         (~ (v1_relat_1 @ X8)
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (r2_hidden @ X11 @ (k2_relat_1 @ X8))
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ (k1_relat_1 @ X8)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['17'])).
% 0.74/1.00  thf('19', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ X2 @ X0)
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_C_3 @ X1 @ X0)) @ 
% 0.74/1.00             (k1_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['16', '18'])).
% 0.74/1.00  thf('20', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_3 @ X14 @ X15)) = (X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('21', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('22', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('23', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ X2 @ X0)
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_C_3 @ X1 @ X0)) @ X0))),
% 0.74/1.00      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.74/1.00  thf('24', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X0) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_C_3 @ X1 @ X0)) @ X0))),
% 0.74/1.00      inference('condensation', [status(thm)], ['23'])).
% 0.74/1.00  thf('25', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/1.00         (((k1_funct_1 @ (sk_C_3 @ X14 @ X15) @ X16) = (X14))
% 0.74/1.00          | ~ (r2_hidden @ X16 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('26', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) = (k1_xboole_0))
% 0.74/1.00          | ((k1_funct_1 @ (sk_C_3 @ X2 @ X0) @ 
% 0.74/1.00              (sk_D_1 @ X1 @ (sk_C_3 @ X1 @ X0))) = (X2)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['24', '25'])).
% 0.74/1.00  thf('27', plain,
% 0.74/1.00      (![X7 : $i, X8 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.74/1.00          | ((sk_C_2 @ X7 @ X8) = (k1_funct_1 @ X8 @ (sk_D @ X7 @ X8)))
% 0.74/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (v1_relat_1 @ X8))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/1.00  thf('28', plain,
% 0.74/1.00      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.74/1.00      inference('cnf', [status(esa)], [d1_tarski])).
% 0.74/1.00  thf('29', plain,
% 0.74/1.00      (![X0 : $i, X3 : $i]:
% 0.74/1.00         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['28'])).
% 0.74/1.00  thf('30', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (~ (v1_relat_1 @ X1)
% 0.74/1.00          | ~ (v1_funct_1 @ X1)
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ X1)
% 0.74/1.00              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['27', '29'])).
% 0.74/1.00  thf('31', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_3 @ X14 @ X15)) = (X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('32', plain,
% 0.74/1.00      (![X7 : $i, X8 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.74/1.00          | (r2_hidden @ (sk_D @ X7 @ X8) @ (k1_relat_1 @ X8))
% 0.74/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (v1_relat_1 @ X8))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/1.00  thf('33', plain,
% 0.74/1.00      (![X0 : $i, X3 : $i]:
% 0.74/1.00         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['28'])).
% 0.74/1.00  thf('34', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (~ (v1_relat_1 @ X1)
% 0.74/1.00          | ~ (v1_funct_1 @ X1)
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.74/1.00          | (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.74/1.00  thf('35', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) @ X0)
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0)))),
% 0.74/1.00      inference('sup+', [status(thm)], ['31', '34'])).
% 0.74/1.00  thf('36', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('37', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('38', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         ((r2_hidden @ (sk_D @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) @ X0)
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0))))),
% 0.74/1.00      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.74/1.00  thf('39', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/1.00         (((k1_funct_1 @ (sk_C_3 @ X14 @ X15) @ X16) = (X14))
% 0.74/1.00          | ~ (r2_hidden @ X16 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('40', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.74/1.00         (((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_funct_1 @ (sk_C_3 @ X3 @ X0) @ 
% 0.74/1.00              (sk_D @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0))) = (X3)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['38', '39'])).
% 0.74/1.00  thf('41', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X1))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0))))),
% 0.74/1.00      inference('sup+', [status(thm)], ['30', '40'])).
% 0.74/1.00  thf('42', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('43', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('44', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X1))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0))))),
% 0.74/1.00      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.74/1.00  thf('45', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X1 @ X0)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X2))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X1 @ X0)) = (X1)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['44'])).
% 0.74/1.00  thf('46', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) != (X2))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ (sk_C_3 @ X2 @ X1)) = (X2))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X2 @ X1))))),
% 0.74/1.00      inference('eq_fact', [status(thm)], ['45'])).
% 0.74/1.00  thf('47', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i]:
% 0.74/1.00         (((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X2 @ X1)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X2 @ X1)) = (X2)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['46'])).
% 0.74/1.00  thf('48', plain,
% 0.74/1.00      (![X1 : $i, X2 : $i]:
% 0.74/1.00         (((k1_tarski @ X2) = (k2_relat_1 @ (sk_C_3 @ X2 @ X1)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X2) @ (sk_C_3 @ X2 @ X1)) = (X2)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['46'])).
% 0.74/1.00  thf('49', plain,
% 0.74/1.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.74/1.00         (~ (r2_hidden @ (sk_C_2 @ X7 @ X8) @ X7)
% 0.74/1.00          | ((sk_C_2 @ X7 @ X8) != (k1_funct_1 @ X8 @ X9))
% 0.74/1.00          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.74/1.00          | ((X7) = (k2_relat_1 @ X8))
% 0.74/1.00          | ~ (v1_funct_1 @ X8)
% 0.74/1.00          | ~ (v1_relat_1 @ X8))),
% 0.74/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.74/1.00  thf('50', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00              != (k1_funct_1 @ (sk_C_3 @ X0 @ X1) @ X2)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/1.00  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.74/1.00      inference('simplify', [status(thm)], ['14'])).
% 0.74/1.00  thf('52', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('53', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('54', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_3 @ X14 @ X15)) = (X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('55', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ~ (r2_hidden @ X2 @ X1)
% 0.74/1.00          | ((sk_C_2 @ (k1_tarski @ X0) @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00              != (k1_funct_1 @ (sk_C_3 @ X0 @ X1) @ X2)))),
% 0.74/1.00      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.74/1.00  thf('56', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((sk_C_2 @ (k1_tarski @ X0) @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00            != (k1_funct_1 @ (sk_C_3 @ X0 @ X1) @ X2))
% 0.74/1.00          | ~ (r2_hidden @ X2 @ X1)
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.74/1.00      inference('simplify', [status(thm)], ['55'])).
% 0.74/1.00  thf('57', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) != (k1_funct_1 @ (sk_C_3 @ X0 @ X2) @ X1))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X2)))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X2)))
% 0.74/1.00          | ~ (r2_hidden @ X1 @ X2))),
% 0.74/1.00      inference('sup-', [status(thm)], ['47', '56'])).
% 0.74/1.00  thf('58', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (~ (r2_hidden @ X1 @ X2)
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X2)))
% 0.74/1.00          | ((X0) != (k1_funct_1 @ (sk_C_3 @ X0 @ X2) @ X1)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['57'])).
% 0.74/1.00  thf('59', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (((X0) != (X0))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ~ (r2_hidden @ (sk_D_1 @ X2 @ (sk_C_3 @ X2 @ X1)) @ X1))),
% 0.74/1.00      inference('sup-', [status(thm)], ['26', '58'])).
% 0.74/1.00  thf('60', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/1.00         (~ (r2_hidden @ (sk_D_1 @ X2 @ (sk_C_3 @ X2 @ X1)) @ X1)
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1)))
% 0.74/1.00          | ((X1) = (k1_xboole_0)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['59'])).
% 0.74/1.00  thf('61', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X0) = (k1_xboole_0))
% 0.74/1.00          | (r2_hidden @ (sk_D_1 @ X1 @ (sk_C_3 @ X1 @ X0)) @ X0))),
% 0.74/1.00      inference('condensation', [status(thm)], ['23'])).
% 0.74/1.00  thf('62', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((X1) = (k1_xboole_0))
% 0.74/1.00          | ((k1_tarski @ X0) = (k2_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.74/1.00      inference('clc', [status(thm)], ['60', '61'])).
% 0.74/1.00  thf(t15_funct_1, conjecture,
% 0.74/1.00    (![A:$i]:
% 0.74/1.00     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.74/1.00       ( ![B:$i]:
% 0.74/1.00         ( ?[C:$i]:
% 0.74/1.00           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.74/1.00             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.74/1.00             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.74/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.74/1.00    (~( ![A:$i]:
% 0.74/1.00        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.74/1.00          ( ![B:$i]:
% 0.74/1.00            ( ?[C:$i]:
% 0.74/1.00              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.74/1.00                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.74/1.00                ( v1_relat_1 @ C ) ) ) ) ) )),
% 0.74/1.00    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 0.74/1.00  thf('63', plain,
% 0.74/1.00      (![X17 : $i]:
% 0.74/1.00         (((k2_relat_1 @ X17) != (k1_tarski @ sk_B))
% 0.74/1.00          | ((k1_relat_1 @ X17) != (sk_A))
% 0.74/1.00          | ~ (v1_funct_1 @ X17)
% 0.74/1.00          | ~ (v1_relat_1 @ X17))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('64', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.74/1.00          | ((k1_relat_1 @ (sk_C_3 @ X0 @ X1)) != (sk_A)))),
% 0.74/1.00      inference('sup-', [status(thm)], ['62', '63'])).
% 0.74/1.00  thf('65', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('66', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_3 @ X14 @ X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('67', plain,
% 0.74/1.00      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_3 @ X14 @ X15)) = (X15))),
% 0.74/1.00      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.74/1.00  thf('68', plain,
% 0.74/1.00      (![X0 : $i, X1 : $i]:
% 0.74/1.00         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 0.74/1.00          | ((X1) = (k1_xboole_0))
% 0.74/1.00          | ((X1) != (sk_A)))),
% 0.74/1.00      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.74/1.00  thf('69', plain,
% 0.74/1.00      (![X0 : $i]:
% 0.74/1.00         (((sk_A) = (k1_xboole_0)) | ((k1_tarski @ X0) != (k1_tarski @ sk_B)))),
% 0.74/1.00      inference('simplify', [status(thm)], ['68'])).
% 0.74/1.00  thf('70', plain, (((sk_A) != (k1_xboole_0))),
% 0.74/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.00  thf('71', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_tarski @ sk_B))),
% 0.74/1.00      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.74/1.00  thf('72', plain, ($false), inference('eq_res', [status(thm)], ['71'])).
% 0.74/1.00  
% 0.74/1.00  % SZS output end Refutation
% 0.74/1.00  
% 0.74/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
