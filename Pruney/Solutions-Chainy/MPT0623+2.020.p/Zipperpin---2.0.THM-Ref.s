%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvBGMIXp76

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:38 EST 2020

% Result     : Theorem 14.22s
% Output     : Refutation 14.22s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 525 expanded)
%              Number of leaves         :   20 ( 170 expanded)
%              Depth                    :   24
%              Number of atoms          : 1251 (5680 expanded)
%              Number of equality atoms :  123 ( 661 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

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

thf('25',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X19 @ X18 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ ( k1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ) @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C @ X1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('53',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0
        = ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X3 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference(condensation,[status(thm)],['62'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','66'])).

thf('68',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('73',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ sk_B )
        | ( X1
          = ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_B ) @ ( sk_D_1 @ X1 @ ( sk_C_2 @ X0 @ sk_B ) ) ) )
        | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ sk_B ) )
        | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('82',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ X1 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ X1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('87',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('90',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('93',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('95',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( sk_B != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( r1_tarski @ X0 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','96'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( r1_tarski @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( sk_B = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ sk_B )
        | ( sk_B = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','102'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('105',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('106',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('108',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ( r2_hidden @ X1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ X0 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','110'])).

thf('113',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('114',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ sk_B ) @ X0 )
        = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('116',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('117',plain,
    ( ! [X0: $i,X1: $i] : ( X1 = X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','111','114','115','116'])).

thf('118',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('119',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','119'])).

thf('121',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('122',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['69','122'])).

thf('124',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HvBGMIXp76
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 14.22/14.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.22/14.47  % Solved by: fo/fo7.sh
% 14.22/14.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.22/14.47  % done 2033 iterations in 14.000s
% 14.22/14.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.22/14.47  % SZS output start Refutation
% 14.22/14.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.22/14.47  thf(sk_B_type, type, sk_B: $i).
% 14.22/14.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.22/14.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.22/14.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.22/14.47  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 14.22/14.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.22/14.47  thf(sk_A_type, type, sk_A: $i).
% 14.22/14.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.22/14.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 14.22/14.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 14.22/14.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.22/14.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.22/14.47  thf(d3_tarski, axiom,
% 14.22/14.47    (![A:$i,B:$i]:
% 14.22/14.47     ( ( r1_tarski @ A @ B ) <=>
% 14.22/14.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 14.22/14.47  thf('0', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf('1', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf(d5_funct_1, axiom,
% 14.22/14.47    (![A:$i]:
% 14.22/14.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.22/14.47       ( ![B:$i]:
% 14.22/14.47         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 14.22/14.47           ( ![C:$i]:
% 14.22/14.47             ( ( r2_hidden @ C @ B ) <=>
% 14.22/14.47               ( ?[D:$i]:
% 14.22/14.47                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 14.22/14.47                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 14.22/14.47  thf('2', plain,
% 14.22/14.47      (![X9 : $i, X11 : $i, X12 : $i]:
% 14.22/14.47         (((X11) != (k2_relat_1 @ X9))
% 14.22/14.47          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 14.22/14.47          | ~ (r2_hidden @ X12 @ X11)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (v1_relat_1 @ X9))),
% 14.22/14.47      inference('cnf', [status(esa)], [d5_funct_1])).
% 14.22/14.47  thf('3', plain,
% 14.22/14.47      (![X9 : $i, X12 : $i]:
% 14.22/14.47         (~ (v1_relat_1 @ X9)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 14.22/14.47          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['2'])).
% 14.22/14.47  thf('4', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 14.22/14.47          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 14.22/14.47              = (k1_funct_1 @ X0 @ 
% 14.22/14.47                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 14.22/14.47          | ~ (v1_funct_1 @ X0)
% 14.22/14.47          | ~ (v1_relat_1 @ X0))),
% 14.22/14.47      inference('sup-', [status(thm)], ['1', '3'])).
% 14.22/14.47  thf(s3_funct_1__e2_24__funct_1, axiom,
% 14.22/14.47    (![A:$i,B:$i]:
% 14.22/14.47     ( ?[C:$i]:
% 14.22/14.47       ( ( ![D:$i]:
% 14.22/14.47           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 14.22/14.47         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 14.22/14.47         ( v1_relat_1 @ C ) ) ))).
% 14.22/14.47  thf('5', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('6', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf('7', plain,
% 14.22/14.47      (![X9 : $i, X11 : $i, X12 : $i]:
% 14.22/14.47         (((X11) != (k2_relat_1 @ X9))
% 14.22/14.47          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 14.22/14.47          | ~ (r2_hidden @ X12 @ X11)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (v1_relat_1 @ X9))),
% 14.22/14.47      inference('cnf', [status(esa)], [d5_funct_1])).
% 14.22/14.47  thf('8', plain,
% 14.22/14.47      (![X9 : $i, X12 : $i]:
% 14.22/14.47         (~ (v1_relat_1 @ X9)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 14.22/14.47          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 14.22/14.47      inference('simplify', [status(thm)], ['7'])).
% 14.22/14.47  thf('9', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 14.22/14.47          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 14.22/14.47             (k1_relat_1 @ X0))
% 14.22/14.47          | ~ (v1_funct_1 @ X0)
% 14.22/14.47          | ~ (v1_relat_1 @ X0))),
% 14.22/14.47      inference('sup-', [status(thm)], ['6', '8'])).
% 14.22/14.47  thf('10', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 14.22/14.47          | ~ (r2_hidden @ X17 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('11', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (~ (v1_relat_1 @ X0)
% 14.22/14.47          | ~ (v1_funct_1 @ X0)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 14.22/14.47          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 14.22/14.47              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['9', '10'])).
% 14.22/14.47  thf('12', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 14.22/14.47            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 14.22/14.47             (sk_C_2 @ X2 @ X0)))
% 14.22/14.47            = (X1))
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 14.22/14.47      inference('sup+', [status(thm)], ['5', '11'])).
% 14.22/14.47  thf('13', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('14', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('15', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 14.22/14.47            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 14.22/14.47             (sk_C_2 @ X2 @ X0)))
% 14.22/14.47            = (X1))
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 14.22/14.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 14.22/14.47  thf('16', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 14.22/14.47      inference('sup+', [status(thm)], ['4', '15'])).
% 14.22/14.47  thf('17', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('18', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('19', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 14.22/14.47      inference('demod', [status(thm)], ['16', '17', '18'])).
% 14.22/14.47  thf('20', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 14.22/14.47          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 14.22/14.47      inference('simplify', [status(thm)], ['19'])).
% 14.22/14.47  thf('21', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf('22', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (~ (r2_hidden @ X0 @ X1)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 14.22/14.47      inference('sup-', [status(thm)], ['20', '21'])).
% 14.22/14.47  thf('23', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 14.22/14.47          | ~ (r2_hidden @ X0 @ X1))),
% 14.22/14.47      inference('simplify', [status(thm)], ['22'])).
% 14.22/14.47  thf('24', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ X0 @ X1)
% 14.22/14.47          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ X0) @ X2)) @ X0))),
% 14.22/14.47      inference('sup-', [status(thm)], ['0', '23'])).
% 14.22/14.47  thf(t18_funct_1, conjecture,
% 14.22/14.47    (![A:$i,B:$i]:
% 14.22/14.47     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 14.22/14.47          ( ![C:$i]:
% 14.22/14.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 14.22/14.47              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 14.22/14.47                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 14.22/14.47  thf(zf_stmt_0, negated_conjecture,
% 14.22/14.47    (~( ![A:$i,B:$i]:
% 14.22/14.47        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 14.22/14.47             ( ![C:$i]:
% 14.22/14.47               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 14.22/14.47                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 14.22/14.47                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 14.22/14.47    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 14.22/14.47  thf('25', plain,
% 14.22/14.47      (![X20 : $i]:
% 14.22/14.47         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 14.22/14.47          | ((sk_B) != (k1_relat_1 @ X20))
% 14.22/14.47          | ~ (v1_funct_1 @ X20)
% 14.22/14.47          | ~ (v1_relat_1 @ X20))),
% 14.22/14.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.47  thf('26', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ sk_A @ X1)
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 14.22/14.47          | ((sk_B) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['24', '25'])).
% 14.22/14.47  thf('27', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('28', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('29', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('30', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B) != (X0)))),
% 14.22/14.47      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 14.22/14.47  thf('31', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 14.22/14.47      inference('simplify', [status(thm)], ['30'])).
% 14.22/14.47  thf('32', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf('33', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 14.22/14.47          | ~ (r2_hidden @ X17 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('34', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ X0 @ X1)
% 14.22/14.47          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['32', '33'])).
% 14.22/14.47  thf('35', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf(t65_relat_1, axiom,
% 14.22/14.47    (![A:$i]:
% 14.22/14.47     ( ( v1_relat_1 @ A ) =>
% 14.22/14.47       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 14.22/14.47         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 14.22/14.47  thf('36', plain,
% 14.22/14.47      (![X7 : $i]:
% 14.22/14.47         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 14.22/14.47          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 14.22/14.47          | ~ (v1_relat_1 @ X7))),
% 14.22/14.47      inference('cnf', [status(esa)], [t65_relat_1])).
% 14.22/14.47  thf('37', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         (((X0) != (k1_xboole_0))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 14.22/14.47          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['35', '36'])).
% 14.22/14.47  thf('38', plain,
% 14.22/14.47      (![X1 : $i]:
% 14.22/14.47         (((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 14.22/14.47      inference('simplify', [status(thm)], ['37'])).
% 14.22/14.47  thf('39', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('40', plain,
% 14.22/14.47      (![X1 : $i]: ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 14.22/14.47      inference('demod', [status(thm)], ['38', '39'])).
% 14.22/14.47  thf('41', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf(t12_funct_1, axiom,
% 14.22/14.47    (![A:$i,B:$i]:
% 14.22/14.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.22/14.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 14.22/14.47         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 14.22/14.47  thf('42', plain,
% 14.22/14.47      (![X18 : $i, X19 : $i]:
% 14.22/14.47         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 14.22/14.47          | (r2_hidden @ (k1_funct_1 @ X19 @ X18) @ (k2_relat_1 @ X19))
% 14.22/14.47          | ~ (v1_funct_1 @ X19)
% 14.22/14.47          | ~ (v1_relat_1 @ X19))),
% 14.22/14.47      inference('cnf', [status(esa)], [t12_funct_1])).
% 14.22/14.47  thf('43', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 14.22/14.47          | ~ (v1_relat_1 @ X0)
% 14.22/14.47          | ~ (v1_funct_1 @ X0)
% 14.22/14.47          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_C @ X1 @ (k1_relat_1 @ X0))) @ 
% 14.22/14.47             (k2_relat_1 @ X0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['41', '42'])).
% 14.22/14.47  thf('44', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r2_hidden @ 
% 14.22/14.47           (k1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 14.22/14.47            (sk_C @ X1 @ (k1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)))) @ 
% 14.22/14.47           k1_xboole_0)
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 14.22/14.47          | (r1_tarski @ (k1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1))),
% 14.22/14.47      inference('sup+', [status(thm)], ['40', '43'])).
% 14.22/14.47  thf('45', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('46', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('47', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('48', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('49', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r2_hidden @ 
% 14.22/14.47           (k1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 14.22/14.47            (sk_C @ X1 @ k1_xboole_0)) @ 
% 14.22/14.47           k1_xboole_0)
% 14.22/14.47          | (r1_tarski @ k1_xboole_0 @ X1))),
% 14.22/14.47      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 14.22/14.47  thf('50', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r2_hidden @ X0 @ k1_xboole_0)
% 14.22/14.47          | (r1_tarski @ k1_xboole_0 @ X1)
% 14.22/14.47          | (r1_tarski @ k1_xboole_0 @ X1))),
% 14.22/14.47      inference('sup+', [status(thm)], ['34', '49'])).
% 14.22/14.47  thf('51', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('simplify', [status(thm)], ['50'])).
% 14.22/14.47  thf('52', plain,
% 14.22/14.47      (![X1 : $i]: ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 14.22/14.47      inference('demod', [status(thm)], ['38', '39'])).
% 14.22/14.47  thf('53', plain,
% 14.22/14.47      (![X9 : $i, X12 : $i]:
% 14.22/14.47         (~ (v1_relat_1 @ X9)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 14.22/14.47          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['2'])).
% 14.22/14.47  thf('54', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 14.22/14.47          | ((X1)
% 14.22/14.47              = (k1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 14.22/14.47                 (sk_D_1 @ X1 @ (sk_C_2 @ X0 @ k1_xboole_0))))
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['52', '53'])).
% 14.22/14.47  thf('55', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('56', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('57', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 14.22/14.47          | ((X1)
% 14.22/14.47              = (k1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 14.22/14.47                 (sk_D_1 @ X1 @ (sk_C_2 @ X0 @ k1_xboole_0)))))),
% 14.22/14.47      inference('demod', [status(thm)], ['54', '55', '56'])).
% 14.22/14.47  thf('58', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X2)
% 14.22/14.47          | ((X0)
% 14.22/14.47              = (k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 14.22/14.47                 (sk_D_1 @ X0 @ (sk_C_2 @ X1 @ k1_xboole_0)))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['51', '57'])).
% 14.22/14.47  thf('59', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('simplify', [status(thm)], ['50'])).
% 14.22/14.47  thf('60', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 14.22/14.47          | ~ (r2_hidden @ X17 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('61', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X2)
% 14.22/14.47          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ X0) = (X1)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['59', '60'])).
% 14.22/14.47  thf('62', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.22/14.47         (((X0) = (X1))
% 14.22/14.47          | (r1_tarski @ k1_xboole_0 @ X3)
% 14.22/14.47          | (r1_tarski @ k1_xboole_0 @ X2))),
% 14.22/14.47      inference('sup+', [status(thm)], ['58', '61'])).
% 14.22/14.47  thf('63', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (((X0) = (X1)) | (r1_tarski @ k1_xboole_0 @ X2))),
% 14.22/14.47      inference('condensation', [status(thm)], ['62'])).
% 14.22/14.47  thf(d10_xboole_0, axiom,
% 14.22/14.47    (![A:$i,B:$i]:
% 14.22/14.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.22/14.47  thf('64', plain,
% 14.22/14.47      (![X4 : $i, X6 : $i]:
% 14.22/14.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 14.22/14.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.22/14.47  thf('65', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.47         (((X1) = (X2))
% 14.22/14.47          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 14.22/14.47          | ((X0) = (k1_xboole_0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['63', '64'])).
% 14.22/14.47  thf('66', plain,
% 14.22/14.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('condensation', [status(thm)], ['65'])).
% 14.22/14.47  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 14.22/14.47      inference('sup-', [status(thm)], ['31', '66'])).
% 14.22/14.47  thf('68', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 14.22/14.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.47  thf('69', plain,
% 14.22/14.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('70', plain,
% 14.22/14.47      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 14.22/14.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.22/14.47  thf('71', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 14.22/14.47      inference('simplify', [status(thm)], ['70'])).
% 14.22/14.47  thf('72', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('73', plain,
% 14.22/14.47      (![X1 : $i]: ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 14.22/14.47      inference('demod', [status(thm)], ['38', '39'])).
% 14.22/14.47  thf('74', plain,
% 14.22/14.47      ((![X0 : $i]: ((k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) = (k1_xboole_0)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup+', [status(thm)], ['72', '73'])).
% 14.22/14.47  thf('75', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('76', plain,
% 14.22/14.47      ((![X0 : $i]: ((k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) = (sk_B)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('demod', [status(thm)], ['74', '75'])).
% 14.22/14.47  thf('77', plain,
% 14.22/14.47      (![X9 : $i, X12 : $i]:
% 14.22/14.47         (~ (v1_relat_1 @ X9)
% 14.22/14.47          | ~ (v1_funct_1 @ X9)
% 14.22/14.47          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 14.22/14.47          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['2'])).
% 14.22/14.47  thf('78', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]:
% 14.22/14.47          (~ (r2_hidden @ X1 @ sk_B)
% 14.22/14.47           | ((X1)
% 14.22/14.47               = (k1_funct_1 @ (sk_C_2 @ X0 @ sk_B) @ 
% 14.22/14.47                  (sk_D_1 @ X1 @ (sk_C_2 @ X0 @ sk_B))))
% 14.22/14.47           | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ sk_B))
% 14.22/14.47           | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ sk_B))))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['76', '77'])).
% 14.22/14.47  thf('79', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 14.22/14.47      inference('simplify', [status(thm)], ['70'])).
% 14.22/14.47  thf('80', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('81', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('simplify', [status(thm)], ['50'])).
% 14.22/14.47  thf('82', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]:
% 14.22/14.47          ((r1_tarski @ sk_B @ X0) | (r2_hidden @ X1 @ k1_xboole_0)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup+', [status(thm)], ['80', '81'])).
% 14.22/14.47  thf('83', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('84', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]:
% 14.22/14.47          ((r1_tarski @ sk_B @ X0) | (r2_hidden @ X1 @ sk_B)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('demod', [status(thm)], ['82', '83'])).
% 14.22/14.47  thf('85', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('86', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X1) | (r2_hidden @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('simplify', [status(thm)], ['50'])).
% 14.22/14.47  thf('87', plain,
% 14.22/14.47      (![X1 : $i, X3 : $i]:
% 14.22/14.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 14.22/14.47      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.47  thf('88', plain,
% 14.22/14.47      (![X0 : $i, X1 : $i]:
% 14.22/14.47         ((r1_tarski @ k1_xboole_0 @ X1) | (r1_tarski @ X0 @ k1_xboole_0))),
% 14.22/14.47      inference('sup-', [status(thm)], ['86', '87'])).
% 14.22/14.47  thf('89', plain,
% 14.22/14.47      (![X1 : $i]: ((k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 14.22/14.47      inference('demod', [status(thm)], ['38', '39'])).
% 14.22/14.47  thf('90', plain,
% 14.22/14.47      (![X20 : $i]:
% 14.22/14.47         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 14.22/14.47          | ((sk_B) != (k1_relat_1 @ X20))
% 14.22/14.47          | ~ (v1_funct_1 @ X20)
% 14.22/14.47          | ~ (v1_relat_1 @ X20))),
% 14.22/14.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.47  thf('91', plain,
% 14.22/14.47      (![X0 : $i]:
% 14.22/14.47         (~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 14.22/14.47          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 14.22/14.47          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 14.22/14.47          | ((sk_B) != (k1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['89', '90'])).
% 14.22/14.47  thf('92', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('93', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('94', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('95', plain,
% 14.22/14.47      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 14.22/14.47      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 14.22/14.47  thf('96', plain,
% 14.22/14.47      (![X0 : $i]: ((r1_tarski @ X0 @ k1_xboole_0) | ((sk_B) != (k1_xboole_0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['88', '95'])).
% 14.22/14.47  thf('97', plain,
% 14.22/14.47      ((![X0 : $i]: (((sk_B) != (sk_B)) | (r1_tarski @ X0 @ k1_xboole_0)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['85', '96'])).
% 14.22/14.47  thf('98', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('99', plain,
% 14.22/14.47      ((![X0 : $i]: (((sk_B) != (sk_B)) | (r1_tarski @ X0 @ sk_B)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('demod', [status(thm)], ['97', '98'])).
% 14.22/14.47  thf('100', plain,
% 14.22/14.47      ((![X0 : $i]: (r1_tarski @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['99'])).
% 14.22/14.47  thf('101', plain,
% 14.22/14.47      (![X4 : $i, X6 : $i]:
% 14.22/14.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 14.22/14.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.22/14.47  thf('102', plain,
% 14.22/14.47      ((![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | ((sk_B) = (X0))))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['100', '101'])).
% 14.22/14.47  thf('103', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ sk_B) | ((sk_B) = (X0))))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['84', '102'])).
% 14.22/14.47  thf('104', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('105', plain,
% 14.22/14.47      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 14.22/14.47      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 14.22/14.47  thf('106', plain,
% 14.22/14.47      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (k1_xboole_0))))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['104', '105'])).
% 14.22/14.47  thf('107', plain,
% 14.22/14.47      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('108', plain,
% 14.22/14.47      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (sk_B))))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('demod', [status(thm)], ['106', '107'])).
% 14.22/14.47  thf('109', plain,
% 14.22/14.47      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['108'])).
% 14.22/14.47  thf('110', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]:
% 14.22/14.47          (~ (r1_tarski @ X0 @ sk_A) | (r2_hidden @ X1 @ sk_B)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['103', '109'])).
% 14.22/14.47  thf('111', plain,
% 14.22/14.47      ((![X0 : $i]: (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['79', '110'])).
% 14.22/14.47  thf('112', plain,
% 14.22/14.47      ((![X0 : $i]: (r2_hidden @ X0 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['79', '110'])).
% 14.22/14.47  thf('113', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 14.22/14.47         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 14.22/14.47          | ~ (r2_hidden @ X17 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('114', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]: ((k1_funct_1 @ (sk_C_2 @ X1 @ sk_B) @ X0) = (X1)))
% 14.22/14.47         <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['112', '113'])).
% 14.22/14.47  thf('115', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('116', plain,
% 14.22/14.47      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 14.22/14.47      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 14.22/14.47  thf('117', plain,
% 14.22/14.47      ((![X0 : $i, X1 : $i]: ((X1) = (X0))) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('demod', [status(thm)], ['78', '111', '114', '115', '116'])).
% 14.22/14.47  thf('118', plain,
% 14.22/14.47      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('simplify', [status(thm)], ['108'])).
% 14.22/14.47  thf('119', plain,
% 14.22/14.47      ((![X0 : $i]: ~ (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 14.22/14.47      inference('sup-', [status(thm)], ['117', '118'])).
% 14.22/14.47  thf('120', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 14.22/14.47      inference('sup-', [status(thm)], ['71', '119'])).
% 14.22/14.47  thf('121', plain,
% 14.22/14.47      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 14.22/14.47      inference('split', [status(esa)], ['68'])).
% 14.22/14.47  thf('122', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 14.22/14.47      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 14.22/14.47  thf('123', plain, (((sk_A) != (k1_xboole_0))),
% 14.22/14.47      inference('simpl_trail', [status(thm)], ['69', '122'])).
% 14.22/14.47  thf('124', plain, ($false),
% 14.22/14.47      inference('simplify_reflect-', [status(thm)], ['67', '123'])).
% 14.22/14.47  
% 14.22/14.47  % SZS output end Refutation
% 14.22/14.47  
% 14.22/14.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
