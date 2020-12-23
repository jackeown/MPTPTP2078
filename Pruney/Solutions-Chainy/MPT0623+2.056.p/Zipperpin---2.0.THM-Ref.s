%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXUXlghu0W

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  177 (2570 expanded)
%              Number of leaves         :   22 ( 834 expanded)
%              Depth                    :   39
%              Number of atoms          : 1990 (36394 expanded)
%              Number of equality atoms :  170 (3223 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) @ X13 )
        = X11 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('9',plain,(
    ! [X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( X9
       != ( k1_funct_1 @ X5 @ X10 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('10',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ X2 ) @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

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

thf('22',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) )
      | ( sk_B_1 != X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B_1 ) ) @ ( k1_relat_1 @ ( sk_C_2 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('37',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B_1 ) ) @ X1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','52'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t16_funct_1,axiom,(
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

thf('55',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( sk_B @ X14 ) )
        = X14 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('56',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( v1_relat_1 @ ( sk_B @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('57',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_B @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('58',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( sk_B @ X14 ) )
        = X14 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C_4 @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_C_4 @ X1 @ ( sk_B @ X0 ) ) @ ( k1_relat_1 @ ( sk_B @ X0 ) ) )
      | ( ( sk_B @ X0 )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( sk_B @ ( k1_relat_1 @ X1 ) )
        = X1 )
      | ( r2_hidden @ ( sk_C_4 @ X1 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) ) @ ( k1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_B @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) ) @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('71',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','73'])).

thf('75',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('81',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 != X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X0 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X1 @ sk_A ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_2 @ X1 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_2 @ X1 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_2 @ X1 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_2 @ X1 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('93',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 != X0 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( sk_B @ sk_A )
        = ( sk_C_2 @ X1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('99',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_C_3 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('100',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( v1_relat_1 @ ( sk_C_3 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('101',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( sk_C_3 @ X14 ) )
        = X14 ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C_4 @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( X1
        = ( sk_C_3 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_3 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( k1_relat_1 @ X1 ) ) )
      | ( X1
        = ( sk_C_3 @ ( k1_relat_1 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ ( k1_relat_1 @ X1 ) ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) )
      | ( X0
        = ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ X0 ) @ ( sk_C_2 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_C_3 @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['98','108'])).

thf('110',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('111',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('113',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('114',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ X0 ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( sk_C_3 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( ( sk_C_2 @ X0 @ sk_A )
        = ( sk_C_3 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['97','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ sk_A )
        = ( sk_C_3 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( sk_B @ sk_A )
      = ( sk_C_3 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','117'])).

thf('119',plain,
    ( ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( ( sk_B @ sk_A )
      = ( sk_C_3 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( sk_B @ X14 )
       != ( sk_C_3 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_funct_1])).

thf('121',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_4 @ ( sk_C_3 @ sk_A ) @ ( sk_B @ sk_A ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('129',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('130',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 != X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130'])).

thf('132',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['133'])).

thf('135',plain,
    ( ( sk_B_1 = sk_A )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['132','134'])).

thf('136',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['131'])).

thf('137',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['133'])).

thf('138',plain,
    ( ( sk_A != sk_A )
   <= ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['133'])).

thf('141',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['139','140'])).

thf('142',plain,(
    sk_B_1 = sk_A ),
    inference(simpl_trail,[status(thm)],['135','141'])).

thf('143',plain,(
    sk_B_1 = sk_A ),
    inference(simpl_trail,[status(thm)],['135','141'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_A ) ) @ X1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','142','143'])).

thf('145',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    sk_B_1 = sk_A ),
    inference(simpl_trail,[status(thm)],['135','141'])).

thf('147',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_A
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X1 @ sk_A ) ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X1 @ sk_A ) ) @ X0 ) )
      | ( sk_A
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X1 @ sk_A ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('150',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('151',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('152',plain,(
    ! [X0: $i] : ( sk_A != X0 ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    $false ),
    inference(simplify,[status(thm)],['152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXUXlghu0W
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.66/2.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.66/2.84  % Solved by: fo/fo7.sh
% 2.66/2.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.84  % done 1070 iterations in 2.385s
% 2.66/2.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.66/2.84  % SZS output start Refutation
% 2.66/2.84  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 2.66/2.84  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.66/2.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.66/2.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.66/2.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.66/2.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.66/2.84  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 2.66/2.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.66/2.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.66/2.84  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.84  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 2.66/2.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.66/2.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.66/2.84  thf(sk_B_type, type, sk_B: $i > $i).
% 2.66/2.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.66/2.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.66/2.84  thf(s3_funct_1__e2_24__funct_1, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ?[C:$i]:
% 2.66/2.84       ( ( ![D:$i]:
% 2.66/2.84           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 2.66/2.84         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 2.66/2.84         ( v1_relat_1 @ C ) ) ))).
% 2.66/2.84  thf('0', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf(d3_tarski, axiom,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ( r1_tarski @ A @ B ) <=>
% 2.66/2.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.66/2.84  thf('1', plain,
% 2.66/2.84      (![X1 : $i, X3 : $i]:
% 2.66/2.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf(d5_funct_1, axiom,
% 2.66/2.84    (![A:$i]:
% 2.66/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.66/2.84       ( ![B:$i]:
% 2.66/2.84         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.66/2.84           ( ![C:$i]:
% 2.66/2.84             ( ( r2_hidden @ C @ B ) <=>
% 2.66/2.84               ( ?[D:$i]:
% 2.66/2.84                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.66/2.84                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.66/2.84  thf('2', plain,
% 2.66/2.84      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.66/2.84         (((X7) != (k2_relat_1 @ X5))
% 2.66/2.84          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 2.66/2.84          | ~ (r2_hidden @ X8 @ X7)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (v1_relat_1 @ X5))),
% 2.66/2.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.66/2.84  thf('3', plain,
% 2.66/2.84      (![X5 : $i, X8 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X5)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.66/2.84          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['2'])).
% 2.66/2.84  thf('4', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['1', '3'])).
% 2.66/2.84  thf('5', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.66/2.84         (((k1_funct_1 @ (sk_C_2 @ X11 @ X12) @ X13) = (X11))
% 2.66/2.84          | ~ (r2_hidden @ X13 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('6', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 2.66/2.84              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['4', '5'])).
% 2.66/2.84  thf('7', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['1', '3'])).
% 2.66/2.84  thf('8', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('9', plain,
% 2.66/2.84      (![X5 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 2.66/2.84         (((X7) != (k2_relat_1 @ X5))
% 2.66/2.84          | (r2_hidden @ X9 @ X7)
% 2.66/2.84          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.66/2.84          | ((X9) != (k1_funct_1 @ X5 @ X10))
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (v1_relat_1 @ X5))),
% 2.66/2.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.66/2.84  thf('10', plain,
% 2.66/2.84      (![X5 : $i, X10 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X5)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 2.66/2.84          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['9'])).
% 2.66/2.84  thf('11', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X2 @ X0)
% 2.66/2.84          | (r2_hidden @ (k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ X2) @ 
% 2.66/2.84             (k2_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['8', '10'])).
% 2.66/2.84  thf('12', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('13', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('14', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X2 @ X0)
% 2.66/2.84          | (r2_hidden @ (k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ X2) @ 
% 2.66/2.84             (k2_relat_1 @ (sk_C_2 @ X1 @ X0))))),
% 2.66/2.84      inference('demod', [status(thm)], ['11', '12', '13'])).
% 2.66/2.84  thf('15', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | (r2_hidden @ 
% 2.66/2.84             (k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 2.66/2.84              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) @ 
% 2.66/2.84             (k2_relat_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['7', '14'])).
% 2.66/2.84  thf('16', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_2 @ X0 @ (k1_relat_1 @ X1))))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | ~ (v1_relat_1 @ X1)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | ~ (v1_relat_1 @ X1))),
% 2.66/2.84      inference('sup+', [status(thm)], ['6', '15'])).
% 2.66/2.84  thf('17', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X1)
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X1) @ X2)
% 2.66/2.84          | (r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_2 @ X0 @ (k1_relat_1 @ X1)))))),
% 2.66/2.84      inference('simplify', [status(thm)], ['16'])).
% 2.66/2.84  thf('18', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.84         ((r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X3)
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 2.66/2.84      inference('sup+', [status(thm)], ['0', '17'])).
% 2.66/2.84  thf('19', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('20', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('21', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.84         ((r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X3))),
% 2.66/2.84      inference('demod', [status(thm)], ['18', '19', '20'])).
% 2.66/2.84  thf(t18_funct_1, conjecture,
% 2.66/2.84    (![A:$i,B:$i]:
% 2.66/2.84     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 2.66/2.84          ( ![C:$i]:
% 2.66/2.84            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.66/2.84              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 2.66/2.84                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 2.66/2.84  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.84    (~( ![A:$i,B:$i]:
% 2.66/2.84        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 2.66/2.84             ( ![C:$i]:
% 2.66/2.84               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.66/2.84                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 2.66/2.84                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 2.66/2.84    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 2.66/2.84  thf('22', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('23', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X1 @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['21', '22'])).
% 2.66/2.84  thf('24', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('25', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('26', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('27', plain,
% 2.66/2.84      (![X0 : $i, X2 : $i]:
% 2.66/2.84         ((r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)))
% 2.66/2.84          | ((sk_B_1) != (X0)))),
% 2.66/2.84      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 2.66/2.84  thf('28', plain,
% 2.66/2.84      (![X2 : $i]: (r2_hidden @ X2 @ (k2_relat_1 @ (sk_C_2 @ X2 @ sk_B_1)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['27'])).
% 2.66/2.84  thf('29', plain,
% 2.66/2.84      (![X5 : $i, X8 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X5)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.66/2.84          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['2'])).
% 2.66/2.84  thf('30', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B_1)) @ 
% 2.66/2.84           (k1_relat_1 @ (sk_C_2 @ X0 @ sk_B_1)))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ sk_B_1))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ sk_B_1)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['28', '29'])).
% 2.66/2.84  thf('31', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('32', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('33', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('34', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (r2_hidden @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B_1)) @ sk_B_1)),
% 2.66/2.84      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 2.66/2.84  thf('35', plain,
% 2.66/2.84      (![X1 : $i, X3 : $i]:
% 2.66/2.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('36', plain,
% 2.66/2.84      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.66/2.84         (((X7) != (k2_relat_1 @ X5))
% 2.66/2.84          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 2.66/2.84          | ~ (r2_hidden @ X8 @ X7)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (v1_relat_1 @ X5))),
% 2.66/2.84      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.66/2.84  thf('37', plain,
% 2.66/2.84      (![X5 : $i, X8 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X5)
% 2.66/2.84          | ~ (v1_funct_1 @ X5)
% 2.66/2.84          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 2.66/2.84          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 2.66/2.84      inference('simplify', [status(thm)], ['36'])).
% 2.66/2.84  thf('38', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 2.66/2.84              = (k1_funct_1 @ X0 @ 
% 2.66/2.84                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['35', '37'])).
% 2.66/2.84  thf('39', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('40', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 2.66/2.84          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 2.66/2.84              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['4', '5'])).
% 2.66/2.84  thf('41', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.84         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 2.66/2.84            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 2.66/2.84             (sk_C_2 @ X2 @ X0)))
% 2.66/2.84            = (X1))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 2.66/2.84      inference('sup+', [status(thm)], ['39', '40'])).
% 2.66/2.84  thf('42', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('43', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('44', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.66/2.84         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 2.66/2.84            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 2.66/2.84             (sk_C_2 @ X2 @ X0)))
% 2.66/2.84            = (X1))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 2.66/2.84      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.66/2.84  thf('45', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 2.66/2.84      inference('sup+', [status(thm)], ['38', '44'])).
% 2.66/2.84  thf('46', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('47', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('48', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 2.66/2.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 2.66/2.84  thf('49', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 2.66/2.84          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['48'])).
% 2.66/2.84  thf('50', plain,
% 2.66/2.84      (![X1 : $i, X3 : $i]:
% 2.66/2.84         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('51', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X0 @ X1)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 2.66/2.84      inference('sup-', [status(thm)], ['49', '50'])).
% 2.66/2.84  thf('52', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 2.66/2.84          | ~ (r2_hidden @ X0 @ X1))),
% 2.66/2.84      inference('simplify', [status(thm)], ['51'])).
% 2.66/2.84  thf('53', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (r1_tarski @ 
% 2.66/2.84          (k2_relat_1 @ (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B_1)) @ X1)) @ 
% 2.66/2.84          sk_B_1)),
% 2.66/2.84      inference('sup-', [status(thm)], ['34', '52'])).
% 2.66/2.84  thf('54', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf(t16_funct_1, axiom,
% 2.66/2.84    (![A:$i]:
% 2.66/2.84     ( ( ![B:$i]:
% 2.66/2.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.66/2.84           ( ![C:$i]:
% 2.66/2.84             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.66/2.84               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 2.66/2.84                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 2.66/2.84                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 2.66/2.84       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.66/2.84  thf('55', plain,
% 2.66/2.84      (![X14 : $i]:
% 2.66/2.84         (((X14) = (k1_xboole_0)) | ((k1_relat_1 @ (sk_B @ X14)) = (X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('56', plain,
% 2.66/2.84      (![X14 : $i]: (((X14) = (k1_xboole_0)) | (v1_relat_1 @ (sk_B @ X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('57', plain,
% 2.66/2.84      (![X14 : $i]: (((X14) = (k1_xboole_0)) | (v1_funct_1 @ (sk_B @ X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('58', plain,
% 2.66/2.84      (![X14 : $i]:
% 2.66/2.84         (((X14) = (k1_xboole_0)) | ((k1_relat_1 @ (sk_B @ X14)) = (X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf(t9_funct_1, axiom,
% 2.66/2.84    (![A:$i]:
% 2.66/2.84     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.66/2.84       ( ![B:$i]:
% 2.66/2.84         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.66/2.84           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.66/2.84               ( ![C:$i]:
% 2.66/2.84                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.66/2.84                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.66/2.84             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.66/2.84  thf('59', plain,
% 2.66/2.84      (![X15 : $i, X16 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X15)
% 2.66/2.84          | ~ (v1_funct_1 @ X15)
% 2.66/2.84          | ((X16) = (X15))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X15 @ X16) @ (k1_relat_1 @ X16))
% 2.66/2.84          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 2.66/2.84          | ~ (v1_funct_1 @ X16)
% 2.66/2.84          | ~ (v1_relat_1 @ X16))),
% 2.66/2.84      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.66/2.84  thf('60', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((X0) != (k1_relat_1 @ X1))
% 2.66/2.84          | ((X0) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_B @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_B @ X0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X1 @ (sk_B @ X0)) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ X0)))
% 2.66/2.84          | ((sk_B @ X0) = (X1))
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | ~ (v1_relat_1 @ X1))),
% 2.66/2.84      inference('sup-', [status(thm)], ['58', '59'])).
% 2.66/2.84  thf('61', plain,
% 2.66/2.84      (![X1 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X1)
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X1)) = (X1))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X1 @ (sk_B @ (k1_relat_1 @ X1))) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ (k1_relat_1 @ X1))))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_B @ (k1_relat_1 @ X1)))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_B @ (k1_relat_1 @ X1)))
% 2.66/2.84          | ((k1_relat_1 @ X1) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['60'])).
% 2.66/2.84  thf('62', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_B @ (k1_relat_1 @ X0)))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ (k1_relat_1 @ X0))))
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['57', '61'])).
% 2.66/2.84  thf('63', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ (k1_relat_1 @ X0))))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_B @ (k1_relat_1 @ X0)))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['62'])).
% 2.66/2.84  thf('64', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ (k1_relat_1 @ X0))))
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['56', '63'])).
% 2.66/2.84  thf('65', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84             (k1_relat_1 @ (sk_B @ (k1_relat_1 @ X0))))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['64'])).
% 2.66/2.84  thf('66', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84           (k1_relat_1 @ X0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0))),
% 2.66/2.84      inference('sup+', [status(thm)], ['55', '65'])).
% 2.66/2.84  thf('67', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ X0)) = (X0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 2.66/2.84             (k1_relat_1 @ X0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['66'])).
% 2.66/2.84  thf('68', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ (sk_C_2 @ X1 @ X0) @ (sk_B @ X0)) @ 
% 2.66/2.84           (k1_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 2.66/2.84          | ((k1_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 2.66/2.84          | ((sk_B @ (k1_relat_1 @ (sk_C_2 @ X1 @ X0))) = (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0)))),
% 2.66/2.84      inference('sup+', [status(thm)], ['54', '67'])).
% 2.66/2.84  thf('69', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('70', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('71', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('72', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('73', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('74', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ (sk_C_2 @ X1 @ X0) @ (sk_B @ X0)) @ X0)
% 2.66/2.84          | ((X0) = (k1_xboole_0))
% 2.66/2.84          | ((sk_B @ X0) = (sk_C_2 @ X1 @ X0)))),
% 2.66/2.84      inference('demod', [status(thm)], ['68', '69', '70', '71', '72', '73'])).
% 2.66/2.84  thf('75', plain,
% 2.66/2.84      (![X1 : $i, X3 : $i]:
% 2.66/2.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('76', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 2.66/2.84          | ~ (r2_hidden @ X0 @ X1))),
% 2.66/2.84      inference('simplify', [status(thm)], ['51'])).
% 2.66/2.84  thf('77', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ X0 @ X1)
% 2.66/2.84          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ X0) @ X2)) @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['75', '76'])).
% 2.66/2.84  thf('78', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('79', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r1_tarski @ sk_A @ X1)
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['77', '78'])).
% 2.66/2.84  thf('80', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('81', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('82', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('83', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) != (X0)))),
% 2.66/2.84      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 2.66/2.84  thf('84', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 2.66/2.84      inference('simplify', [status(thm)], ['83'])).
% 2.66/2.84  thf('85', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (~ (r2_hidden @ X0 @ X1)
% 2.66/2.84          | (r2_hidden @ X0 @ X2)
% 2.66/2.84          | ~ (r1_tarski @ X1 @ X2))),
% 2.66/2.84      inference('cnf', [status(esa)], [d3_tarski])).
% 2.66/2.84  thf('86', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 2.66/2.84      inference('sup-', [status(thm)], ['84', '85'])).
% 2.66/2.84  thf('87', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((sk_B @ sk_A) = (sk_C_2 @ X0 @ sk_A))
% 2.66/2.84          | ((sk_A) = (k1_xboole_0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_2 @ X0 @ sk_A) @ (sk_B @ sk_A)) @ X1))),
% 2.66/2.84      inference('sup-', [status(thm)], ['74', '86'])).
% 2.66/2.84  thf('88', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 2.66/2.84          | ~ (r2_hidden @ X0 @ X1))),
% 2.66/2.84      inference('simplify', [status(thm)], ['51'])).
% 2.66/2.84  thf('89', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0))
% 2.66/2.84          | ((sk_B @ sk_A) = (sk_C_2 @ X1 @ sk_A))
% 2.66/2.84          | (r1_tarski @ 
% 2.66/2.84             (k2_relat_1 @ 
% 2.66/2.84              (sk_C_2 @ (sk_C_4 @ (sk_C_2 @ X1 @ sk_A) @ (sk_B @ sk_A)) @ X2)) @ 
% 2.66/2.84             X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['87', '88'])).
% 2.66/2.84  thf('90', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('91', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((sk_B @ sk_A) = (sk_C_2 @ X1 @ sk_A))
% 2.66/2.84          | ((sk_A) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ 
% 2.66/2.84               (sk_C_2 @ (sk_C_4 @ (sk_C_2 @ X1 @ sk_A) @ (sk_B @ sk_A)) @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ 
% 2.66/2.84               (sk_C_2 @ (sk_C_4 @ (sk_C_2 @ X1 @ sk_A) @ (sk_B @ sk_A)) @ X0))
% 2.66/2.84          | ((sk_B_1)
% 2.66/2.84              != (k1_relat_1 @ 
% 2.66/2.84                  (sk_C_2 @ (sk_C_4 @ (sk_C_2 @ X1 @ sk_A) @ (sk_B @ sk_A)) @ 
% 2.66/2.84                   X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['89', '90'])).
% 2.66/2.84  thf('92', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('93', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('94', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('95', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((sk_B @ sk_A) = (sk_C_2 @ X1 @ sk_A))
% 2.66/2.84          | ((sk_A) = (k1_xboole_0))
% 2.66/2.84          | ((sk_B_1) != (X0)))),
% 2.66/2.84      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 2.66/2.84  thf('96', plain,
% 2.66/2.84      (![X1 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_C_2 @ X1 @ sk_A)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['95'])).
% 2.66/2.84  thf('97', plain,
% 2.66/2.84      (![X1 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0)) | ((sk_B @ sk_A) = (sk_C_2 @ X1 @ sk_A)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['95'])).
% 2.66/2.84  thf('98', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('99', plain,
% 2.66/2.84      (![X14 : $i]: (((X14) = (k1_xboole_0)) | (v1_funct_1 @ (sk_C_3 @ X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('100', plain,
% 2.66/2.84      (![X14 : $i]: (((X14) = (k1_xboole_0)) | (v1_relat_1 @ (sk_C_3 @ X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('101', plain,
% 2.66/2.84      (![X14 : $i]:
% 2.66/2.84         (((X14) = (k1_xboole_0)) | ((k1_relat_1 @ (sk_C_3 @ X14)) = (X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('102', plain,
% 2.66/2.84      (![X15 : $i, X16 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ X15)
% 2.66/2.84          | ~ (v1_funct_1 @ X15)
% 2.66/2.84          | ((X16) = (X15))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ X15 @ X16) @ (k1_relat_1 @ X16))
% 2.66/2.84          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 2.66/2.84          | ~ (v1_funct_1 @ X16)
% 2.66/2.84          | ~ (v1_relat_1 @ X16))),
% 2.66/2.84      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.66/2.84  thf('103', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((k1_relat_1 @ X1) != (X0))
% 2.66/2.84          | ((X0) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ X1)
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ X0) @ X1) @ (k1_relat_1 @ X1))
% 2.66/2.84          | ((X1) = (sk_C_3 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_3 @ X0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_3 @ X0)))),
% 2.66/2.84      inference('sup-', [status(thm)], ['101', '102'])).
% 2.66/2.84  thf('104', plain,
% 2.66/2.84      (![X1 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ (sk_C_3 @ (k1_relat_1 @ X1)))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_3 @ (k1_relat_1 @ X1)))
% 2.66/2.84          | ((X1) = (sk_C_3 @ (k1_relat_1 @ X1)))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ (k1_relat_1 @ X1)) @ X1) @ 
% 2.66/2.84             (k1_relat_1 @ X1))
% 2.66/2.84          | ~ (v1_funct_1 @ X1)
% 2.66/2.84          | ~ (v1_relat_1 @ X1)
% 2.66/2.84          | ((k1_relat_1 @ X1) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['103'])).
% 2.66/2.84  thf('105', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ((X0) = (sk_C_3 @ (k1_relat_1 @ X0)))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_3 @ (k1_relat_1 @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['100', '104'])).
% 2.66/2.84  thf('106', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (~ (v1_funct_1 @ (sk_C_3 @ (k1_relat_1 @ X0)))
% 2.66/2.84          | ((X0) = (sk_C_3 @ (k1_relat_1 @ X0)))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0)
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['105'])).
% 2.66/2.84  thf('107', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ X0)
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ((X0) = (sk_C_3 @ (k1_relat_1 @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['99', '106'])).
% 2.66/2.84  thf('108', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((X0) = (sk_C_3 @ (k1_relat_1 @ X0)))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.66/2.84             (k1_relat_1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ X0)
% 2.66/2.84          | ~ (v1_relat_1 @ X0)
% 2.66/2.84          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['107'])).
% 2.66/2.84  thf('109', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ (sk_C_3 @ X0) @ (sk_C_2 @ X1 @ X0)) @ 
% 2.66/2.84           (k1_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 2.66/2.84          | ((k1_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 2.66/2.84          | ((sk_C_2 @ X1 @ X0) = (sk_C_3 @ (k1_relat_1 @ (sk_C_2 @ X1 @ X0)))))),
% 2.66/2.84      inference('sup+', [status(thm)], ['98', '108'])).
% 2.66/2.84  thf('110', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('111', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('112', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('113', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('114', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('115', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ (sk_C_3 @ X0) @ (sk_C_2 @ X1 @ X0)) @ X0)
% 2.66/2.84          | ((X0) = (k1_xboole_0))
% 2.66/2.84          | ((sk_C_2 @ X1 @ X0) = (sk_C_3 @ X0)))),
% 2.66/2.84      inference('demod', [status(thm)],
% 2.66/2.84                ['109', '110', '111', '112', '113', '114'])).
% 2.66/2.84  thf('116', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         ((r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ sk_A)
% 2.66/2.84          | ((sk_A) = (k1_xboole_0))
% 2.66/2.84          | ((sk_C_2 @ X0 @ sk_A) = (sk_C_3 @ sk_A))
% 2.66/2.84          | ((sk_A) = (k1_xboole_0)))),
% 2.66/2.84      inference('sup+', [status(thm)], ['97', '115'])).
% 2.66/2.84  thf('117', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((sk_C_2 @ X0 @ sk_A) = (sk_C_3 @ sk_A))
% 2.66/2.84          | ((sk_A) = (k1_xboole_0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ sk_A))),
% 2.66/2.84      inference('simplify', [status(thm)], ['116'])).
% 2.66/2.84  thf('118', plain,
% 2.66/2.84      ((((sk_B @ sk_A) = (sk_C_3 @ sk_A))
% 2.66/2.84        | ((sk_A) = (k1_xboole_0))
% 2.66/2.84        | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ sk_A)
% 2.66/2.84        | ((sk_A) = (k1_xboole_0)))),
% 2.66/2.84      inference('sup+', [status(thm)], ['96', '117'])).
% 2.66/2.84  thf('119', plain,
% 2.66/2.84      (((r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ sk_A)
% 2.66/2.84        | ((sk_A) = (k1_xboole_0))
% 2.66/2.84        | ((sk_B @ sk_A) = (sk_C_3 @ sk_A)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['118'])).
% 2.66/2.84  thf('120', plain,
% 2.66/2.84      (![X14 : $i]:
% 2.66/2.84         (((X14) = (k1_xboole_0)) | ((sk_B @ X14) != (sk_C_3 @ X14)))),
% 2.66/2.84      inference('cnf', [status(esa)], [t16_funct_1])).
% 2.66/2.84  thf('121', plain,
% 2.66/2.84      ((((sk_A) = (k1_xboole_0))
% 2.66/2.84        | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ sk_A))),
% 2.66/2.84      inference('clc', [status(thm)], ['119', '120'])).
% 2.66/2.84  thf('122', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 2.66/2.84      inference('sup-', [status(thm)], ['84', '85'])).
% 2.66/2.84  thf('123', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0))
% 2.66/2.84          | (r2_hidden @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['121', '122'])).
% 2.66/2.84  thf('124', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.84         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 2.66/2.84          | ~ (r2_hidden @ X0 @ X1))),
% 2.66/2.84      inference('simplify', [status(thm)], ['51'])).
% 2.66/2.84  thf('125', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0))
% 2.66/2.84          | (r1_tarski @ 
% 2.66/2.84             (k2_relat_1 @ 
% 2.66/2.84              (sk_C_2 @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ X1)) @ 
% 2.66/2.84             X0))),
% 2.66/2.84      inference('sup-', [status(thm)], ['123', '124'])).
% 2.66/2.84  thf('126', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('127', plain,
% 2.66/2.84      (![X0 : $i]:
% 2.66/2.84         (((sk_A) = (k1_xboole_0))
% 2.66/2.84          | ~ (v1_relat_1 @ 
% 2.66/2.84               (sk_C_2 @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ 
% 2.66/2.84               (sk_C_2 @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ X0))
% 2.66/2.84          | ((sk_B_1)
% 2.66/2.84              != (k1_relat_1 @ 
% 2.66/2.84                  (sk_C_2 @ (sk_C_4 @ (sk_C_3 @ sk_A) @ (sk_B @ sk_A)) @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['125', '126'])).
% 2.66/2.84  thf('128', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('129', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('130', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('131', plain,
% 2.66/2.84      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B_1) != (X0)))),
% 2.66/2.84      inference('demod', [status(thm)], ['127', '128', '129', '130'])).
% 2.66/2.84  thf('132', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.84      inference('simplify', [status(thm)], ['131'])).
% 2.66/2.84  thf('133', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('134', plain,
% 2.66/2.84      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.66/2.84      inference('split', [status(esa)], ['133'])).
% 2.66/2.84  thf('135', plain, ((((sk_B_1) = (sk_A))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 2.66/2.84      inference('sup+', [status(thm)], ['132', '134'])).
% 2.66/2.84  thf('136', plain, (((sk_A) = (k1_xboole_0))),
% 2.66/2.84      inference('simplify', [status(thm)], ['131'])).
% 2.66/2.84  thf('137', plain,
% 2.66/2.84      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 2.66/2.84      inference('split', [status(esa)], ['133'])).
% 2.66/2.84  thf('138', plain, ((((sk_A) != (sk_A))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['136', '137'])).
% 2.66/2.84  thf('139', plain, ((((sk_A) = (k1_xboole_0)))),
% 2.66/2.84      inference('simplify', [status(thm)], ['138'])).
% 2.66/2.84  thf('140', plain,
% 2.66/2.84      ((((sk_B_1) = (k1_xboole_0))) | ~ (((sk_A) = (k1_xboole_0)))),
% 2.66/2.84      inference('split', [status(esa)], ['133'])).
% 2.66/2.84  thf('141', plain, ((((sk_B_1) = (k1_xboole_0)))),
% 2.66/2.84      inference('sat_resolution*', [status(thm)], ['139', '140'])).
% 2.66/2.84  thf('142', plain, (((sk_B_1) = (sk_A))),
% 2.66/2.84      inference('simpl_trail', [status(thm)], ['135', '141'])).
% 2.66/2.84  thf('143', plain, (((sk_B_1) = (sk_A))),
% 2.66/2.84      inference('simpl_trail', [status(thm)], ['135', '141'])).
% 2.66/2.84  thf('144', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (r1_tarski @ 
% 2.66/2.84          (k2_relat_1 @ (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_A)) @ X1)) @ 
% 2.66/2.84          sk_A)),
% 2.66/2.84      inference('demod', [status(thm)], ['53', '142', '143'])).
% 2.66/2.84  thf('145', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_B_1) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.84  thf('146', plain, (((sk_B_1) = (sk_A))),
% 2.66/2.84      inference('simpl_trail', [status(thm)], ['135', '141'])).
% 2.66/2.84  thf('147', plain,
% 2.66/2.84      (![X17 : $i]:
% 2.66/2.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 2.66/2.84          | ((sk_A) != (k1_relat_1 @ X17))
% 2.66/2.84          | ~ (v1_funct_1 @ X17)
% 2.66/2.84          | ~ (v1_relat_1 @ X17))),
% 2.66/2.84      inference('demod', [status(thm)], ['145', '146'])).
% 2.66/2.84  thf('148', plain,
% 2.66/2.84      (![X0 : $i, X1 : $i]:
% 2.66/2.84         (~ (v1_relat_1 @ (sk_C_2 @ (sk_D_1 @ X1 @ (sk_C_2 @ X1 @ sk_A)) @ X0))
% 2.66/2.84          | ~ (v1_funct_1 @ 
% 2.66/2.84               (sk_C_2 @ (sk_D_1 @ X1 @ (sk_C_2 @ X1 @ sk_A)) @ X0))
% 2.66/2.84          | ((sk_A)
% 2.66/2.84              != (k1_relat_1 @ 
% 2.66/2.84                  (sk_C_2 @ (sk_D_1 @ X1 @ (sk_C_2 @ X1 @ sk_A)) @ X0))))),
% 2.66/2.84      inference('sup-', [status(thm)], ['144', '147'])).
% 2.66/2.84  thf('149', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('150', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('151', plain,
% 2.66/2.84      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 2.66/2.84      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 2.66/2.84  thf('152', plain, (![X0 : $i]: ((sk_A) != (X0))),
% 2.66/2.84      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 2.66/2.84  thf('153', plain, ($false), inference('simplify', [status(thm)], ['152'])).
% 2.66/2.84  
% 2.66/2.84  % SZS output end Refutation
% 2.66/2.84  
% 2.66/2.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
