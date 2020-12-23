%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UiTf7qo2fe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:32 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  144 (4006 expanded)
%              Number of leaves         :   17 (1240 expanded)
%              Depth                    :   39
%              Number of atoms          : 1442 (42161 expanded)
%              Number of equality atoms :  234 (6469 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_relat_1 @ X13 )
       != sk_A )
      | ( ( k1_relat_1 @ X14 )
       != sk_A )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( ( sk_C @ X1 @ X2 )
        = ( k1_funct_1 @ X2 @ ( sk_D @ X1 @ X2 ) ) )
      | ( X1
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('21',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( X1
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('25',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('28',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('29',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X11 ) @ X12 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_B @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['18'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','34'])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('37',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X11 ) @ X12 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( sk_C @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ sk_A @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( sk_C @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X11 ) @ X12 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = X0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ sk_A @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','26','29'])).

thf('61',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( sk_A
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ k1_xboole_0 ) @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( r2_hidden @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['82'])).

thf('84',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( sk_C @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['82'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['62','68'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['96'])).

thf('98',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['83','97'])).

thf('99',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['106'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','107'])).

thf('109',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r2_hidden @ k1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('114',plain,
    ( ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf('115',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X11 ) @ X12 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('116',plain,
    ( ( sk_A
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['106'])).

thf('118',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','120'])).

thf('122',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    $false ),
    inference(simplify,[status(thm)],['124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UiTf7qo2fe
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 179 iterations in 0.206s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.66  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ?[C:$i]:
% 0.46/0.66       ( ( ![D:$i]:
% 0.46/0.66           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.46/0.66         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.46/0.66         ( v1_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ?[B:$i]:
% 0.46/0.66       ( ( ![C:$i]:
% 0.46/0.66           ( ( r2_hidden @ C @ A ) =>
% 0.46/0.66             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.66         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.46/0.66         ( v1_relat_1 @ B ) ) ))).
% 0.46/0.66  thf('1', plain, (![X11 : $i]: ((k1_relat_1 @ (sk_B @ X11)) = (X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf(t16_funct_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ![B:$i]:
% 0.46/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.66               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.66                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.46/0.66                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.46/0.66       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ![B:$i]:
% 0.46/0.66            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.66                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.46/0.66                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.46/0.66                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.46/0.66          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X13)
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ((X14) = (X13))
% 0.46/0.66          | ((k1_relat_1 @ X13) != (sk_A))
% 0.46/0.66          | ((k1_relat_1 @ X14) != (sk_A))
% 0.46/0.66          | ~ (v1_funct_1 @ X14)
% 0.46/0.66          | ~ (v1_relat_1 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ X1)
% 0.46/0.66          | ~ (v1_funct_1 @ X1)
% 0.46/0.66          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.66          | ((X1) = (sk_B @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain, (![X11 : $i]: (v1_funct_1 @ (sk_B @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('5', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ X1)
% 0.46/0.66          | ~ (v1_funct_1 @ X1)
% 0.46/0.66          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.66          | ((X1) = (sk_B @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X1 : $i]:
% 0.46/0.66         (((X1) = (sk_B @ sk_A))
% 0.46/0.66          | ((k1_relat_1 @ X1) != (sk_A))
% 0.46/0.66          | ~ (v1_funct_1 @ X1)
% 0.46/0.66          | ~ (v1_relat_1 @ X1))),
% 0.46/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (sk_A))
% 0.46/0.66          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.46/0.66          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '7'])).
% 0.46/0.66  thf('9', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('10', plain, (![X8 : $i, X9 : $i]: (v1_funct_1 @ (sk_C_1 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.46/0.66  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
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
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.46/0.66          | ((sk_C @ X1 @ X2) = (k1_funct_1 @ X2 @ (sk_D @ X1 @ X2)))
% 0.46/0.66          | ((X1) = (k2_relat_1 @ X2))
% 0.46/0.66          | ~ (v1_funct_1 @ X2)
% 0.46/0.66          | ~ (v1_relat_1 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('14', plain, (![X11 : $i]: ((k1_relat_1 @ (sk_B @ X11)) = (X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf(t64_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.66           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.66         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) != (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.46/0.66          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.66  thf('17', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.66  thf('19', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('20', plain, (![X11 : $i]: ((k1_relat_1 @ (sk_B @ X11)) = (X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('21', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X1 : $i, X2 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.46/0.66          | (r2_hidden @ (sk_D @ X1 @ X2) @ (k1_relat_1 @ X2))
% 0.46/0.66          | ((X1) = (k2_relat_1 @ X2))
% 0.46/0.66          | ~ (v1_funct_1 @ X2)
% 0.46/0.66          | ~ (v1_relat_1 @ X2))),
% 0.46/0.66      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('25', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('28', plain, (![X11 : $i]: (v1_funct_1 @ (sk_B @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('29', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '26', '29'])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_B @ X11) @ X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_B @ k1_xboole_0) @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.66  thf('33', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['18'])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.46/0.66          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['13', '34'])).
% 0.46/0.66  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('37', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.46/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_B @ X11) @ X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['12', '41'])).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.46/0.66          | ~ (r2_hidden @ X10 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (X0))
% 0.46/0.66          | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['42', '45'])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((sk_C @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_B @ X11) @ X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.66  thf('52', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.46/0.66          | ~ (r2_hidden @ X10 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0)) = (X0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['52', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (X0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['51', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      ((((k1_funct_1 @ k1_xboole_0 @ (sk_D @ sk_A @ k1_xboole_0))
% 0.46/0.66          = (k1_xboole_0))
% 0.46/0.66        | ((sk_A) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '26', '29'])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.46/0.66          | ~ (r2_hidden @ X10 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.46/0.66              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (k1_xboole_0))
% 0.46/0.66          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.46/0.66          | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf('66', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) != (k1_xboole_0)) | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.66  thf('68', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '68'])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (X0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['59', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.66  thf('72', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((sk_A) != (X0))
% 0.46/0.66          | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (((r2_hidden @ (sk_C @ sk_A @ k1_xboole_0) @ sk_A)
% 0.46/0.66        | ((sk_A) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['73'])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (((r2_hidden @ k1_xboole_0 @ sk_A)
% 0.46/0.66        | ((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((sk_A) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['48', '74'])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      ((((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | (r2_hidden @ k1_xboole_0 @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.66  thf('77', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.66  thf('79', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66            = (X0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66            = (X0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['77', '78'])).
% 0.46/0.66  thf('81', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) = (X1))
% 0.46/0.66          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['81'])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['82'])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((sk_C @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['82'])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.46/0.66              = (X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('86', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.66  thf('87', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ k1_xboole_0) = (X0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['88'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) = (X1))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66              = (k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['89', '90'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66            = (k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((X0) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['91'])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      ((((k1_funct_1 @ k1_xboole_0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0))
% 0.46/0.66          = (k1_xboole_0))
% 0.46/0.66        | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['92'])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.66          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '68'])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (X0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | (r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['93', '94'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['95'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (((r2_hidden @ (sk_C @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.46/0.66        | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('condensation', [status(thm)], ['96'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.66        | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['83', '97'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.46/0.66          | ~ (r2_hidden @ X10 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ (sk_C_1 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_funct_1 @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((X0) = (X1))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['103', '104'])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)) | ((X0) = (X1)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['105'])).
% 0.46/0.66  thf('107', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('condensation', [status(thm)], ['106'])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0)) | (r2_hidden @ k1_xboole_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['76', '107'])).
% 0.46/0.66  thf('109', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('110', plain, ((r2_hidden @ k1_xboole_0 @ sk_A)),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.46/0.66          | ~ (r2_hidden @ X10 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      (![X0 : $i]: ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0) = (X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['110', '111'])).
% 0.46/0.66  thf('113', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      ((((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | (r2_hidden @ k1_xboole_0 @ sk_A))),
% 0.46/0.66      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         (((k1_funct_1 @ (sk_B @ X11) @ X12) = (k1_xboole_0))
% 0.46/0.66          | ~ (r2_hidden @ X12 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      ((((sk_A) = (k2_relat_1 @ k1_xboole_0))
% 0.46/0.66        | ((k1_funct_1 @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.66  thf('117', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.46/0.66      inference('condensation', [status(thm)], ['106'])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      ((((sk_A) = (k1_xboole_0))
% 0.46/0.66        | ((k1_funct_1 @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.66  thf('119', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      (((k1_funct_1 @ (sk_B @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['113', '120'])).
% 0.46/0.66  thf('122', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 0.46/0.66      inference('sup+', [status(thm)], ['112', '121'])).
% 0.46/0.66  thf('123', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('124', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.66  thf('125', plain, ($false), inference('simplify', [status(thm)], ['124'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.51/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
