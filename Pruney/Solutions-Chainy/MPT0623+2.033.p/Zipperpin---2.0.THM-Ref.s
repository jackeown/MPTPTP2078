%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3LVUyOovM

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 199 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  891 (1697 expanded)
%              Number of equality atoms :  139 ( 280 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_zfmisc_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

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

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X30 @ X31 ) )
        = X31 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('14',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X30 @ X31 ) )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('18',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X30 @ X31 ) )
        = ( k1_tarski @ X30 ) )
      | ( X31 = k1_xboole_0 ) ) ),
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

thf('25',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('35',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('40',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('41',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','42'])).

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

thf('44',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( sk_B @ X28 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X28: $i] :
      ( v1_funct_1 @ ( sk_B @ X28 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('51',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['33','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','55'])).

thf('57',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('60',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('67',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('73',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','73'])).

thf('75',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('77',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('78',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('80',plain,
    ( ( sk_B_1
      = ( k6_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('82',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','82'])).

thf('84',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('85',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('86',plain,
    ( ( ( sk_B @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('88',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X28: $i] :
      ( v1_funct_1 @ ( sk_B @ X28 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('90',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['83','90'])).

thf('92',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('93',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['58','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( sk_D @ sk_A @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['56','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('97',plain,(
    $false ),
    inference('sup-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H3LVUyOovM
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 114 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.50  thf(d4_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.50         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.50  thf(t12_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.20/0.50         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X20 @ X21) = (k1_xboole_0))
% 0.20/0.50          | ((X21) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X20 : $i]: ((k2_zfmisc_1 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.50  thf(t152_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]: ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.50  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.50          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.50  thf(t2_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X24 @ X25)) = (k3_xboole_0 @ X24 @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.20/0.50          | ((X1) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.50  thf(t15_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ?[C:$i]:
% 0.20/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         (((k1_relat_1 @ (sk_C_2 @ X30 @ X31)) = (X31))
% 0.20/0.50          | ((X31) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (sk_C_2 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         ((v1_funct_1 @ (sk_C_2 @ X30 @ X31)) | ((X31) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.20/0.50          | ((X15) = (X12))
% 0.20/0.50          | ((X14) != (k1_tarski @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X12 : $i, X15 : $i]:
% 0.20/0.50         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.50          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X30 : $i, X31 : $i]:
% 0.20/0.50         (((k2_relat_1 @ (sk_C_2 @ X30 @ X31)) = (k1_tarski @ X30))
% 0.20/0.50          | ((X31) = (k1_xboole_0)))),
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
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X32 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.50          | ~ (v1_funct_1 @ X32)
% 0.20/0.50          | ~ (v1_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.50          | ((X1) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X0)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.20/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.20/0.50          | ((X1) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X1)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_A @ X1)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((sk_B_1) != (X0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | ((X0) = (k1_xboole_0))
% 0.20/0.50          | (r1_tarski @ sk_A @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.50  thf(t60_relat_1, axiom,
% 0.20/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('34', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X32 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.50          | ~ (v1_funct_1 @ X32)
% 0.20/0.50          | ~ (v1_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.50        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('37', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.50        | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.50  thf('40', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('41', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( ![C:$i]:
% 0.20/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('44', plain, (![X28 : $i]: ((k1_relat_1 @ (sk_B @ X28)) = (X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf(t64_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X27 : $i]:
% 0.20/0.50         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 0.20/0.50          | ((X27) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X27))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((X0) != (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.50          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, (![X28 : $i]: (v1_relat_1 @ (sk_B @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.50  thf('50', plain, (![X28 : $i]: (v1_funct_1 @ (sk_B @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('51', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '51'])).
% 0.20/0.50  thf('53', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['33', '52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((sk_A) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '55'])).
% 0.20/0.50  thf('57', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('60', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (![X32 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X32) @ sk_A)
% 0.20/0.50          | ((sk_B_1) != (k1_relat_1 @ X32))
% 0.20/0.50          | ~ (v1_funct_1 @ X32)
% 0.20/0.50          | ~ (v1_relat_1 @ X32))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.20/0.50         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.50         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('67', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.50         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '68', '73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('77', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((sk_B_1) = (k6_relat_1 @ sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('82', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('85', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      ((((sk_B @ sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.50  thf('89', plain, (![X28 : $i]: (v1_funct_1 @ (sk_B @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.50  thf('90', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['88', '89'])).
% 0.20/0.50  thf('91', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['83', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['57'])).
% 0.20/0.50  thf('93', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['91', '92'])).
% 0.20/0.50  thf('94', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['58', '93'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ (sk_D @ sk_A @ k1_xboole_0 @ X0) @ X1)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['56', '94'])).
% 0.20/0.50  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('97', plain, ($false), inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
