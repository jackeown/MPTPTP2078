%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bH7rbozLF

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 145 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  755 (1297 expanded)
%              Number of equality atoms :  109 ( 194 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X25 @ X26 ) )
        = X26 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( X8 = X5 )
      | ( X7
       != ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8 = X5 )
      | ~ ( r2_hidden @ X8 @ ( k1_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

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

thf('30',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('40',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('41',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','45'])).

thf('47',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('51',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( ( k2_relat_1 @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_relat_1 @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ sk_B_1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('62',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('65',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('66',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('67',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','63','64','65','66'])).

thf('68',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['47'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ sk_A @ k1_xboole_0 ) @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['46','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('74',plain,(
    $false ),
    inference('sup-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0bH7rbozLF
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:56:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 85 iterations in 0.049s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.50  thf(d4_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X17 : $i, X20 : $i]:
% 0.20/0.50         (((X20) = (k1_relat_1 @ X17))
% 0.20/0.50          | (r2_hidden @ 
% 0.20/0.50             (k4_tarski @ (sk_C_2 @ X20 @ X17) @ (sk_D @ X20 @ X17)) @ X17)
% 0.20/0.50          | (r2_hidden @ (sk_C_2 @ X20 @ X17) @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 0.20/0.50          | ((X12) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.50  thf(t152_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]: ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.50  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.50          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.50  thf(t60_relat_1, axiom,
% 0.20/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('6', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf(t15_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ?[C:$i]:
% 0.20/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (((k1_relat_1 @ (sk_C_3 @ X25 @ X26)) = (X26))
% 0.20/0.50          | ((X26) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (sk_C_3 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         ((v1_funct_1 @ (sk_C_3 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ X7) | ((X8) = (X5)) | ((X7) != (k1_tarski @ X5)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X5 : $i, X8 : $i]:
% 0.20/0.50         (((X8) = (X5)) | ~ (r2_hidden @ X8 @ (k1_tarski @ X5)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.50          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (sk_C_3 @ X25 @ X26)) = (k1_tarski @ X25))
% 0.20/0.50          | ((X26) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf(t18_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50          ( ![C:$i]:
% 0.20/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.50                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.50                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X27 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.50          | ~ (v1_funct_1 @ X27)
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.50          | ((X1) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X0)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.50          | ((X1) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X1)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X1)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((sk_B_1) != (X0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( ![C:$i]:
% 0.20/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('30', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf(t65_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X22 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.50          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) != (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X27 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.50          | ~ (v1_funct_1 @ X27)
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.50        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.50        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.20/0.50        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('38', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('39', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('40', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('41', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.20/0.50  thf('43', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['29', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_A) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '45'])).
% 0.20/0.50  thf('47', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['47'])).
% 0.20/0.50  thf('49', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['47'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X22 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.20/0.50          | ((k2_relat_1 @ X22) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.50           | ~ (v1_relat_1 @ X0)
% 0.20/0.50           | ((k2_relat_1 @ X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['47'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.20/0.50           | ~ (v1_relat_1 @ X0)
% 0.20/0.50           | ((k2_relat_1 @ X0) = (sk_B_1))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((X0) != (sk_B_1))
% 0.20/0.50           | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))
% 0.20/0.50           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '54'])).
% 0.20/0.50  thf('56', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((X0) != (sk_B_1)) | ((k2_relat_1 @ (sk_B @ X0)) = (sk_B_1))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((((k2_relat_1 @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X27 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.20/0.50          | ~ (v1_funct_1 @ X27)
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.50         | ~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.20/0.50         | ~ (v1_funct_1 @ (sk_B @ sk_B_1))
% 0.20/0.50         | ((sk_B_1) != (k1_relat_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['47'])).
% 0.20/0.50  thf('62', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('65', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('66', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['60', '63', '64', '65', '66'])).
% 0.20/0.50  thf('68', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['47'])).
% 0.20/0.50  thf('70', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.20/0.50  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['48', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X0 : $i]: (r2_hidden @ (sk_C_2 @ sk_A @ k1_xboole_0) @ X0)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['46', '71'])).
% 0.20/0.50  thf('73', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('74', plain, ($false), inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
