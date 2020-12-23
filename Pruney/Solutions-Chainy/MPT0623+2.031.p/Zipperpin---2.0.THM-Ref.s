%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5MrNAmBjsG

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 293 expanded)
%              Number of leaves         :   29 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  835 (2656 expanded)
%              Number of equality atoms :  134 ( 455 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X20 @ X17 ) @ ( sk_D @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_2 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

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

thf('6',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('13',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','13'])).

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

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X26 @ X27 ) )
        = X27 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X26 @ X27 ) )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X26 @ X27 ) )
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 ) ) ),
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

thf('28',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('41',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('49',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('50',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('51',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('53',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47','48','51','52'])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['36','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','56'])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('62',plain,
    ( ( ( sk_B @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('64',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('66',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('68',plain,
    ( ( ( sk_B_1 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('70',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('71',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('72',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('74',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69','72','73'])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('79',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('80',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('82',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('83',plain,(
    ! [X24: $i] :
      ( v1_funct_1 @ ( sk_B @ X24 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('84',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('86',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','80','81','84','85'])).

thf('87',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['57','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('93',plain,(
    $false ),
    inference('sup-',[status(thm)],['91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5MrNAmBjsG
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:22:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 104 iterations in 0.068s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(d4_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X17 : $i, X20 : $i]:
% 0.21/0.55         (((X20) = (k1_relat_1 @ X17))
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C_2 @ X20 @ X17) @ (sk_D @ X20 @ X17)) @ X17)
% 0.21/0.55          | (r2_hidden @ (sk_C_2 @ X20 @ X17) @ X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.55  thf(t113_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X11 : $i, X12 : $i]:
% 0.21/0.55         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.21/0.55          | ((X12) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.55  thf(t152_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.55  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.55          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.55  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ?[B:$i]:
% 0.21/0.55       ( ( ![C:$i]:
% 0.21/0.55           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.55             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.55         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.55         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.55  thf('6', plain, (![X24 : $i]: ((k1_relat_1 @ (sk_B @ X24)) = (X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf(t64_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.55         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X22 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.21/0.55          | ((X22) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((X0) != (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.55          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain, (![X24 : $i]: (v1_relat_1 @ (sk_B @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('12', plain, (![X24 : $i]: ((k1_relat_1 @ (sk_B @ X24)) = (X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('13', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.55          | ((X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['5', '13'])).
% 0.21/0.55  thf(t15_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ?[C:$i]:
% 0.21/0.55           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.55             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.55             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (((k1_relat_1 @ (sk_C_3 @ X26 @ X27)) = (X27))
% 0.21/0.55          | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (sk_C_3 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         ((v1_funct_1 @ (sk_C_3 @ X26 @ X27)) | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf(d1_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X5 : $i, X8 : $i]:
% 0.21/0.55         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.55          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.21/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ X0 @ X1)
% 0.21/0.55          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['18', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (sk_C_3 @ X26 @ X27)) = (k1_tarski @ X26))
% 0.21/0.55          | ((X27) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.55  thf(t18_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.55          ( ![C:$i]:
% 0.21/0.55            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.55                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.55             ( ![C:$i]:
% 0.21/0.55               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.55                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X28 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.21/0.55          | ~ (v1_funct_1 @ X28)
% 0.21/0.55          | ~ (v1_relat_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.55          | ((X1) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.21/0.55          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X0)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.21/0.55          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.21/0.55          | ((X1) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k1_xboole_0))
% 0.21/0.55          | ((X0) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.55          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X1)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.21/0.55          | ((X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k1_xboole_0))
% 0.21/0.55          | ((X0) = (k1_xboole_0))
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.55          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['16', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_A @ X1)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.21/0.55          | ((X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((sk_B_1) != (X0))
% 0.21/0.55          | ((X0) = (k1_xboole_0))
% 0.21/0.55          | ((X0) = (k1_xboole_0))
% 0.21/0.55          | (r1_tarski @ sk_A @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.55  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf(t65_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.55         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.21/0.55          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.55        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('41', plain, (![X24 : $i]: (v1_relat_1 @ (sk_B @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['39', '42'])).
% 0.21/0.55  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X28 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.21/0.55          | ~ (v1_funct_1 @ X28)
% 0.21/0.55          | ~ (v1_relat_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.55        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.55        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.55        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.55  thf('47', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.55  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('49', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('50', plain, (![X24 : $i]: (v1_funct_1 @ (sk_B @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('51', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('53', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '47', '48', '51', '52'])).
% 0.21/0.55  thf('54', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['36', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_A) = (k1_xboole_0))
% 0.21/0.55          | (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '56'])).
% 0.21/0.55  thf('58', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('61', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      ((((sk_B @ sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('65', plain, (![X24 : $i]: ((k1_relat_1 @ (sk_B @ X24)) = (X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.21/0.55          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      (((((sk_B_1) != (k1_xboole_0))
% 0.21/0.55         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.55         | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))))
% 0.21/0.55         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.55  thf('72', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('73', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('74', plain,
% 0.21/0.55      (((((sk_B_1) != (sk_B_1)) | ((k2_relat_1 @ sk_B_1) = (sk_B_1))))
% 0.21/0.55         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['68', '69', '72', '73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      (![X28 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k2_relat_1 @ X28) @ sk_A)
% 0.21/0.55          | ((sk_B_1) != (k1_relat_1 @ X28))
% 0.21/0.55          | ~ (v1_funct_1 @ X28)
% 0.21/0.55          | ~ (v1_relat_1 @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.55         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.55         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.55         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.55         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('79', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.55  thf('80', plain,
% 0.21/0.55      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.55         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.55  thf('81', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['70', '71'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('83', plain, (![X24 : $i]: (v1_funct_1 @ (sk_B @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.55  thf('84', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['82', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['77', '80', '81', '84', '85'])).
% 0.21/0.55  thf('87', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['86'])).
% 0.21/0.55  thf('88', plain,
% 0.21/0.55      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('split', [status(esa)], ['58'])).
% 0.21/0.55  thf('89', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.21/0.55  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['59', '89'])).
% 0.21/0.55  thf('91', plain,
% 0.21/0.55      (![X0 : $i]: (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0)),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['57', '90'])).
% 0.21/0.55  thf('92', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.55  thf('93', plain, ($false), inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
