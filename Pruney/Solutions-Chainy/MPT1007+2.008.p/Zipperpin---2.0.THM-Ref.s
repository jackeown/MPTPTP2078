%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P7wEckhzuk

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 376 expanded)
%              Number of leaves         :   40 ( 127 expanded)
%              Depth                    :   23
%              Number of atoms          :  738 (4116 expanded)
%              Number of equality atoms :   50 ( 221 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( sk_B @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X23 ) @ ( sk_C @ X23 ) ) @ X23 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('14',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X23 ) @ ( sk_C @ X23 ) ) @ X23 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X22 )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('21',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( r2_hidden @ ( k4_tarski @ X25 @ X28 ) @ X26 )
      | ( X28
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( r2_hidden @ ( k4_tarski @ X25 @ ( k1_funct_1 @ X26 @ X25 ) ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('29',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('33',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['3','35'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ sk_B_2 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('39',plain,(
    ! [X24: $i] :
      ( ( v1_funct_1 @ X24 )
      | ~ ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ( X27
       != ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( ( k1_funct_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('44',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('45',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('57',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('60',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','54','57','60'])).

thf('62',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','34'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('67',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','67'])).

thf('69',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','68'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('70',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('71',plain,(
    $false ),
    inference('sup-',[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P7wEckhzuk
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 171 iterations in 0.096s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i > $i).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(existence_m1_subset_1, axiom,
% 0.39/0.56    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.39/0.56  thf('0', plain, (![X13 : $i]: (m1_subset_1 @ (sk_B @ X13) @ X13)),
% 0.39/0.56      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.39/0.56  thf(t2_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X17 : $i, X18 : $i]:
% 0.39/0.56         ((r2_hidden @ X17 @ X18)
% 0.39/0.56          | (v1_xboole_0 @ X18)
% 0.39/0.56          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.39/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.56  thf(t61_funct_2, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.56         ( m1_subset_1 @
% 0.39/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.56         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.56            ( m1_subset_1 @
% 0.39/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.56            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t56_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.39/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X23 : $i]:
% 0.39/0.56         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X23) @ (sk_C @ X23)) @ X23)
% 0.39/0.56          | ((X23) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ X23))),
% 0.39/0.56      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(l3_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X14 @ X15)
% 0.39/0.56          | (r2_hidden @ X14 @ X16)
% 0.39/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.39/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.39/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.39/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '7'])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( v1_relat_1 @ C ) ))).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.56         ((v1_relat_1 @ X34)
% 0.39/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.56  thf('11', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.39/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('demod', [status(thm)], ['8', '11'])).
% 0.39/0.56  thf(t128_zfmisc_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( r2_hidden @
% 0.39/0.56         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.39/0.56       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.56         (((X9) = (X8))
% 0.39/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.39/0.56               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_1) = (sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X23 : $i]:
% 0.39/0.56         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X23) @ (sk_C @ X23)) @ X23)
% 0.39/0.56          | ((X23) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ X23))),
% 0.39/0.56      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.39/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.39/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.39/0.56        | ((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.39/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.39/0.56  thf(t20_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ C ) =>
% 0.39/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.39/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.39/0.56           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.56         (~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X22)
% 0.39/0.56          | (r2_hidden @ X20 @ (k1_relat_1 @ X22))
% 0.39/0.56          | ~ (v1_relat_1 @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.39/0.56        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.56  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.39/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.56  thf(d4_funct_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.56       ( ![B:$i,C:$i]:
% 0.39/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.39/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.39/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.39/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.39/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i, X28 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.39/0.56          | (r2_hidden @ (k4_tarski @ X25 @ X28) @ X26)
% 0.39/0.56          | ((X28) != (k1_funct_1 @ X26 @ X25))
% 0.39/0.56          | ~ (v1_funct_1 @ X26)
% 0.39/0.56          | ~ (v1_relat_1 @ X26))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X26)
% 0.39/0.56          | ~ (v1_funct_1 @ X26)
% 0.39/0.56          | (r2_hidden @ (k4_tarski @ X25 @ (k1_funct_1 @ X26 @ X25)) @ X26)
% 0.39/0.56          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_1 @ sk_A)) @ 
% 0.39/0.56           sk_C_1)
% 0.39/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.39/0.56        | ~ (v1_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['23', '25'])).
% 0.39/0.56  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_1 @ sk_A)) @ 
% 0.39/0.56           sk_C_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k4_tarski @ sk_A @ (k1_funct_1 @ sk_C_1 @ sk_A)) @ 
% 0.39/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.56         ((r2_hidden @ X10 @ X11)
% 0.39/0.56          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.39/0.56               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      ((((sk_C_1) = (k1_xboole_0))
% 0.39/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('35', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.39/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.39/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.39/0.56      inference('demod', [status(thm)], ['3', '35'])).
% 0.39/0.56  thf(t7_funct_2, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.39/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X40 @ X41)
% 0.39/0.56          | ((X42) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_funct_1 @ X43)
% 0.39/0.56          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.39/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.39/0.56          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ X42))),
% 0.39/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ sk_B_2)
% 0.39/0.56          | ~ (v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.39/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.39/0.56          | ((sk_B_2) = (k1_xboole_0))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf(cc1_funct_1, axiom,
% 0.39/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.39/0.56  thf('39', plain, (![X24 : $i]: ((v1_funct_1 @ X24) | ~ (v1_xboole_0 @ X24))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.39/0.56  thf(t60_relat_1, axiom,
% 0.39/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.39/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.56  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.56         ((r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.39/0.56          | ((X27) = (k1_xboole_0))
% 0.39/0.56          | ((X27) != (k1_funct_1 @ X26 @ X25))
% 0.39/0.56          | ~ (v1_funct_1 @ X26)
% 0.39/0.56          | ~ (v1_relat_1 @ X26))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X26)
% 0.39/0.56          | ~ (v1_funct_1 @ X26)
% 0.39/0.56          | ((k1_funct_1 @ X26 @ X25) = (k1_xboole_0))
% 0.39/0.56          | (r2_hidden @ X25 @ (k1_relat_1 @ X26)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.39/0.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['40', '42'])).
% 0.39/0.56  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.39/0.56  thf('44', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.39/0.56  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.39/0.56  thf('45', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.39/0.56  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.56      inference('sup+', [status(thm)], ['44', '45'])).
% 0.39/0.56  thf('47', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.39/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['43', '46'])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.56          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['39', '47'])).
% 0.39/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.56  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.56          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.56  thf(t7_ordinal1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      (![X32 : $i, X33 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X32 @ X33) | ~ (r1_tarski @ X33 @ X32))),
% 0.39/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.39/0.56  thf('52', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.39/0.56          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.56  thf('53', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.56  thf('55', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('56', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.39/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('57', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.39/0.56      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.56  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('59', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.39/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('60', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.39/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.39/0.56          | ((sk_B_2) = (k1_xboole_0))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['38', '54', '57', '60'])).
% 0.39/0.56  thf('62', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ k1_xboole_0 @ sk_B_2)
% 0.39/0.56          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.39/0.56      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.39/0.56  thf('64', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('65', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.39/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('66', plain,
% 0.39/0.56      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['52', '53'])).
% 0.39/0.56  thf('67', plain, (~ (r2_hidden @ k1_xboole_0 @ sk_B_2)),
% 0.39/0.56      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.39/0.56  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.39/0.56      inference('clc', [status(thm)], ['63', '67'])).
% 0.39/0.56  thf('69', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '68'])).
% 0.39/0.56  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.39/0.56  thf('70', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.39/0.56  thf('71', plain, ($false), inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
