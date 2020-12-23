%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0620+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aTFdHFFNAn

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:12 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 132 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   25
%              Number of atoms          :  824 (1658 expanded)
%              Number of equality atoms :   89 ( 188 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ ( sk_B @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( ( sk_C_1 @ X5 @ X6 )
        = ( k1_funct_1 @ X6 @ ( sk_D @ X5 @ X6 ) ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('11',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X2 )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( sk_C_2 @ X2 @ X1 ) )
        = X2 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X2 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X2 @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X2 @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X2 )
        = ( k2_relat_1 @ ( sk_C_2 @ X2 @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X2 ) @ ( sk_C_2 @ X2 @ X1 ) )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( ( sk_C_1 @ X5 @ X6 )
       != ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( sk_C_2 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( sk_C_2 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['28','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( sk_C_2 @ X0 @ X1 ) )
       != ( k1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_funct_1 @ ( sk_C_2 @ X0 @ X2 ) @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) )
      | ( X0
       != ( k1_funct_1 @ ( sk_C_2 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( v1_xboole_0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ X1 ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_relat_1 @ X21 )
       != sk_A )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ X1 )
      | ( X1 != sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_xboole_0 @ sk_A ),
    inference(eq_res,[status(thm)],['48'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).


%------------------------------------------------------------------------------
