%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coqamW2UXT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:27 EST 2020

% Result     : Theorem 26.85s
% Output     : Refutation 26.85s
% Verified   : 
% Statistics : Number of formulae       :   68 (  87 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   21
%              Number of atoms          :  697 ( 996 expanded)
%              Number of equality atoms :   96 ( 139 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

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

thf('9',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('10',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('14',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('15',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) @ X13 )
        = X11 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = ( k1_tarski @ X3 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = ( k1_tarski @ X3 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( sk_C @ X2 @ X1 )
       != X2 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

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

thf('31',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X14 )
       != sk_A )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ( X1 != sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( sk_C_2 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_C_2 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C_2 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['7','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.coqamW2UXT
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 26.85/27.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.85/27.06  % Solved by: fo/fo7.sh
% 26.85/27.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.85/27.06  % done 9166 iterations in 26.606s
% 26.85/27.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.85/27.06  % SZS output start Refutation
% 26.85/27.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.85/27.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.85/27.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 26.85/27.06  thf(sk_B_type, type, sk_B: $i).
% 26.85/27.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.85/27.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 26.85/27.06  thf(sk_A_type, type, sk_A: $i).
% 26.85/27.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 26.85/27.06  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 26.85/27.06  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 26.85/27.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.85/27.06  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 26.85/27.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.85/27.06  thf(s3_funct_1__e2_24__funct_1, axiom,
% 26.85/27.06    (![A:$i,B:$i]:
% 26.85/27.06     ( ?[C:$i]:
% 26.85/27.06       ( ( ![D:$i]:
% 26.85/27.06           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 26.85/27.06         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 26.85/27.06         ( v1_relat_1 @ C ) ) ))).
% 26.85/27.06  thf('0', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf(t64_relat_1, axiom,
% 26.85/27.06    (![A:$i]:
% 26.85/27.06     ( ( v1_relat_1 @ A ) =>
% 26.85/27.06       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 26.85/27.06           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 26.85/27.06         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 26.85/27.06  thf('1', plain,
% 26.85/27.06      (![X3 : $i]:
% 26.85/27.06         (((k1_relat_1 @ X3) != (k1_xboole_0))
% 26.85/27.06          | ((X3) = (k1_xboole_0))
% 26.85/27.06          | ~ (v1_relat_1 @ X3))),
% 26.85/27.06      inference('cnf', [status(esa)], [t64_relat_1])).
% 26.85/27.06  thf('2', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i]:
% 26.85/27.06         (((X0) != (k1_xboole_0))
% 26.85/27.06          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 26.85/27.06          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 26.85/27.06      inference('sup-', [status(thm)], ['0', '1'])).
% 26.85/27.06  thf('3', plain, (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('4', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i]:
% 26.85/27.06         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 26.85/27.06      inference('demod', [status(thm)], ['2', '3'])).
% 26.85/27.06  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.85/27.06      inference('simplify', [status(thm)], ['4'])).
% 26.85/27.06  thf('6', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.85/27.06      inference('sup+', [status(thm)], ['5', '6'])).
% 26.85/27.06  thf(t41_zfmisc_1, axiom,
% 26.85/27.06    (![A:$i,B:$i]:
% 26.85/27.06     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 26.85/27.06          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 26.85/27.06  thf('8', plain,
% 26.85/27.06      (![X1 : $i, X2 : $i]:
% 26.85/27.06         (((X1) = (k1_xboole_0))
% 26.85/27.06          | (r2_hidden @ (sk_C @ X2 @ X1) @ X1)
% 26.85/27.06          | ((X1) = (k1_tarski @ X2)))),
% 26.85/27.06      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 26.85/27.06  thf(d5_funct_1, axiom,
% 26.85/27.06    (![A:$i]:
% 26.85/27.06     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.85/27.06       ( ![B:$i]:
% 26.85/27.06         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 26.85/27.06           ( ![C:$i]:
% 26.85/27.06             ( ( r2_hidden @ C @ B ) <=>
% 26.85/27.06               ( ?[D:$i]:
% 26.85/27.06                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 26.85/27.06                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 26.85/27.06  thf('9', plain,
% 26.85/27.06      (![X5 : $i, X7 : $i, X8 : $i]:
% 26.85/27.06         (((X7) != (k2_relat_1 @ X5))
% 26.85/27.06          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 26.85/27.06          | ~ (r2_hidden @ X8 @ X7)
% 26.85/27.06          | ~ (v1_funct_1 @ X5)
% 26.85/27.06          | ~ (v1_relat_1 @ X5))),
% 26.85/27.06      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.85/27.06  thf('10', plain,
% 26.85/27.06      (![X5 : $i, X8 : $i]:
% 26.85/27.06         (~ (v1_relat_1 @ X5)
% 26.85/27.06          | ~ (v1_funct_1 @ X5)
% 26.85/27.06          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 26.85/27.06          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 26.85/27.06      inference('simplify', [status(thm)], ['9'])).
% 26.85/27.06  thf('11', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i]:
% 26.85/27.06         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 26.85/27.06          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 26.85/27.06          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 26.85/27.06              = (k1_funct_1 @ X0 @ 
% 26.85/27.06                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 26.85/27.06          | ~ (v1_funct_1 @ X0)
% 26.85/27.06          | ~ (v1_relat_1 @ X0))),
% 26.85/27.06      inference('sup-', [status(thm)], ['8', '10'])).
% 26.85/27.06  thf('12', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('13', plain,
% 26.85/27.06      (![X1 : $i, X2 : $i]:
% 26.85/27.06         (((X1) = (k1_xboole_0))
% 26.85/27.06          | (r2_hidden @ (sk_C @ X2 @ X1) @ X1)
% 26.85/27.06          | ((X1) = (k1_tarski @ X2)))),
% 26.85/27.06      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 26.85/27.06  thf('14', plain,
% 26.85/27.06      (![X5 : $i, X7 : $i, X8 : $i]:
% 26.85/27.06         (((X7) != (k2_relat_1 @ X5))
% 26.85/27.06          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 26.85/27.06          | ~ (r2_hidden @ X8 @ X7)
% 26.85/27.06          | ~ (v1_funct_1 @ X5)
% 26.85/27.06          | ~ (v1_relat_1 @ X5))),
% 26.85/27.06      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.85/27.06  thf('15', plain,
% 26.85/27.06      (![X5 : $i, X8 : $i]:
% 26.85/27.06         (~ (v1_relat_1 @ X5)
% 26.85/27.06          | ~ (v1_funct_1 @ X5)
% 26.85/27.06          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 26.85/27.06          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 26.85/27.06      inference('simplify', [status(thm)], ['14'])).
% 26.85/27.06  thf('16', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i]:
% 26.85/27.06         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 26.85/27.06          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 26.85/27.06          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 26.85/27.06             (k1_relat_1 @ X0))
% 26.85/27.06          | ~ (v1_funct_1 @ X0)
% 26.85/27.06          | ~ (v1_relat_1 @ X0))),
% 26.85/27.06      inference('sup-', [status(thm)], ['13', '15'])).
% 26.85/27.06  thf('17', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i, X13 : $i]:
% 26.85/27.06         (((k1_funct_1 @ (sk_C_2 @ X11 @ X12) @ X13) = (X11))
% 26.85/27.06          | ~ (r2_hidden @ X13 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('18', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.85/27.06         (~ (v1_relat_1 @ X0)
% 26.85/27.06          | ~ (v1_funct_1 @ X0)
% 26.85/27.06          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 26.85/27.06          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 26.85/27.06              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 26.85/27.06      inference('sup-', [status(thm)], ['16', '17'])).
% 26.85/27.06  thf('19', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.85/27.06         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 26.85/27.06            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 26.85/27.06             (sk_C_2 @ X2 @ X0)))
% 26.85/27.06            = (X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_tarski @ X3))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 26.85/27.06          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 26.85/27.06      inference('sup+', [status(thm)], ['12', '18'])).
% 26.85/27.06  thf('20', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('21', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('22', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.85/27.06         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 26.85/27.06            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 26.85/27.06             (sk_C_2 @ X2 @ X0)))
% 26.85/27.06            = (X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_tarski @ X3))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_xboole_0)))),
% 26.85/27.06      inference('demod', [status(thm)], ['19', '20', '21'])).
% 26.85/27.06  thf('23', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.85/27.06         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 26.85/27.06          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 26.85/27.06          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 26.85/27.06      inference('sup+', [status(thm)], ['11', '22'])).
% 26.85/27.06  thf('24', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('25', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.06  thf('26', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.85/27.06         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 26.85/27.06      inference('demod', [status(thm)], ['23', '24', '25'])).
% 26.85/27.06  thf('27', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.85/27.06         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 26.85/27.06          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 26.85/27.06      inference('simplify', [status(thm)], ['26'])).
% 26.85/27.06  thf('28', plain,
% 26.85/27.06      (![X1 : $i, X2 : $i]:
% 26.85/27.06         (((X1) = (k1_xboole_0))
% 26.85/27.06          | ((sk_C @ X2 @ X1) != (X2))
% 26.85/27.06          | ((X1) = (k1_tarski @ X2)))),
% 26.85/27.06      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 26.85/27.06  thf('29', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.85/27.06         (((X0) != (X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0)))),
% 26.85/27.06      inference('sup-', [status(thm)], ['27', '28'])).
% 26.85/27.06  thf('30', plain,
% 26.85/27.06      (![X1 : $i, X2 : $i]:
% 26.85/27.06         (((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_tarski @ X1))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_xboole_0)))),
% 26.85/27.06      inference('simplify', [status(thm)], ['29'])).
% 26.85/27.06  thf(t15_funct_1, conjecture,
% 26.85/27.06    (![A:$i]:
% 26.85/27.06     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 26.85/27.06       ( ![B:$i]:
% 26.85/27.06         ( ?[C:$i]:
% 26.85/27.06           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 26.85/27.06             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 26.85/27.06             ( v1_relat_1 @ C ) ) ) ) ))).
% 26.85/27.06  thf(zf_stmt_0, negated_conjecture,
% 26.85/27.06    (~( ![A:$i]:
% 26.85/27.06        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 26.85/27.06          ( ![B:$i]:
% 26.85/27.06            ( ?[C:$i]:
% 26.85/27.06              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 26.85/27.06                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 26.85/27.06                ( v1_relat_1 @ C ) ) ) ) ) )),
% 26.85/27.06    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 26.85/27.06  thf('31', plain,
% 26.85/27.06      (![X14 : $i]:
% 26.85/27.06         (((k2_relat_1 @ X14) != (k1_tarski @ sk_B))
% 26.85/27.06          | ((k1_relat_1 @ X14) != (sk_A))
% 26.85/27.06          | ~ (v1_funct_1 @ X14)
% 26.85/27.06          | ~ (v1_relat_1 @ X14))),
% 26.85/27.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.85/27.06  thf('32', plain,
% 26.85/27.06      (![X0 : $i, X1 : $i]:
% 26.85/27.06         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 26.85/27.06          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 26.85/27.06          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 26.85/27.06          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 26.85/27.06          | ((k1_relat_1 @ (sk_C_2 @ X0 @ X1)) != (sk_A)))),
% 26.85/27.06      inference('sup-', [status(thm)], ['30', '31'])).
% 26.85/27.06  thf('33', plain,
% 26.85/27.06      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.06      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.07  thf('34', plain,
% 26.85/27.07      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.07      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.07  thf('35', plain,
% 26.85/27.07      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 26.85/27.07      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.07  thf('36', plain,
% 26.85/27.07      (![X0 : $i, X1 : $i]:
% 26.85/27.07         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 26.85/27.07          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 26.85/27.07          | ((X1) != (sk_A)))),
% 26.85/27.07      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 26.85/27.07  thf('37', plain,
% 26.85/27.07      (![X0 : $i]:
% 26.85/27.07         (((k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)) = (k1_xboole_0))
% 26.85/27.07          | ((k1_tarski @ X0) != (k1_tarski @ sk_B)))),
% 26.85/27.07      inference('simplify', [status(thm)], ['36'])).
% 26.85/27.07  thf('38', plain, (((k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 26.85/27.07      inference('eq_res', [status(thm)], ['37'])).
% 26.85/27.07  thf('39', plain,
% 26.85/27.07      (![X3 : $i]:
% 26.85/27.07         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 26.85/27.07          | ((X3) = (k1_xboole_0))
% 26.85/27.07          | ~ (v1_relat_1 @ X3))),
% 26.85/27.07      inference('cnf', [status(esa)], [t64_relat_1])).
% 26.85/27.07  thf('40', plain,
% 26.85/27.07      ((((k1_xboole_0) != (k1_xboole_0))
% 26.85/27.07        | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 26.85/27.07        | ((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 26.85/27.07      inference('sup-', [status(thm)], ['38', '39'])).
% 26.85/27.07  thf('41', plain,
% 26.85/27.07      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 26.85/27.07      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.07  thf('42', plain,
% 26.85/27.07      ((((k1_xboole_0) != (k1_xboole_0))
% 26.85/27.07        | ((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 26.85/27.07      inference('demod', [status(thm)], ['40', '41'])).
% 26.85/27.07  thf('43', plain, (((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0))),
% 26.85/27.07      inference('simplify', [status(thm)], ['42'])).
% 26.85/27.07  thf('44', plain,
% 26.85/27.07      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 26.85/27.07      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.85/27.07  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 26.85/27.07      inference('sup+', [status(thm)], ['43', '44'])).
% 26.85/27.07  thf('46', plain, (((k1_xboole_0) = (sk_A))),
% 26.85/27.07      inference('sup+', [status(thm)], ['7', '45'])).
% 26.85/27.07  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 26.85/27.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.85/27.07  thf('48', plain, ($false),
% 26.85/27.07      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 26.85/27.07  
% 26.85/27.07  % SZS output end Refutation
% 26.85/27.07  
% 26.91/27.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
