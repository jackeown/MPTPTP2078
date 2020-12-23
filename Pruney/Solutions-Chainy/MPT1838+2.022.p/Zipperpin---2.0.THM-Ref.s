%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FmyJdvEkA2

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:17 EST 2020

% Result     : Theorem 0.93s
% Output     : Refutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 148 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  710 (1046 expanded)
%              Number of equality atoms :   72 (  98 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( ~ ( v1_zfmisc_1 @ X36 )
      | ( X36
        = ( k6_domain_1 @ X36 @ ( sk_B_1 @ X36 ) ) )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('3',plain,(
    ! [X36: $i] :
      ( ~ ( v1_zfmisc_1 @ X36 )
      | ( m1_subset_1 @ ( sk_B_1 @ X36 ) @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( ( k6_domain_1 @ X34 @ X35 )
        = ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,
    ( sk_B_2
    = ( k2_xboole_0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = X30 )
      | ( ( k1_tarski @ X31 )
       != ( k2_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_B_2 = sk_A )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( k2_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ sk_B_2 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_B @ sk_A ) @ ( k2_xboole_0 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('36',plain,(
    ! [X26: $i] :
      ( r1_tarski @ k1_xboole_0 @ X26 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( k2_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','52'])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('57',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['35','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_2 @ sk_B_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','71'])).

thf('73',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('74',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','75','76'])).

thf('78',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FmyJdvEkA2
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.93/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.93/1.13  % Solved by: fo/fo7.sh
% 0.93/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.93/1.13  % done 2216 iterations in 0.692s
% 0.93/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.93/1.13  % SZS output start Refutation
% 0.93/1.13  thf(sk_B_type, type, sk_B: $i > $i).
% 0.93/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.93/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.93/1.13  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.93/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.93/1.13  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.93/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.93/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.93/1.13  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.93/1.13  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.93/1.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.93/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.93/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.93/1.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.93/1.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.93/1.13  thf(t1_tex_2, conjecture,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.93/1.13       ( ![B:$i]:
% 0.93/1.13         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.93/1.13           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.93/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.93/1.13    (~( ![A:$i]:
% 0.93/1.13        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.93/1.13          ( ![B:$i]:
% 0.93/1.13            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.93/1.13              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.93/1.13    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.93/1.13  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.93/1.13  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.13  thf(d1_tex_2, axiom,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.93/1.13       ( ( v1_zfmisc_1 @ A ) <=>
% 0.93/1.13         ( ?[B:$i]:
% 0.93/1.13           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.93/1.13  thf('2', plain,
% 0.93/1.13      (![X36 : $i]:
% 0.93/1.13         (~ (v1_zfmisc_1 @ X36)
% 0.93/1.13          | ((X36) = (k6_domain_1 @ X36 @ (sk_B_1 @ X36)))
% 0.93/1.13          | (v1_xboole_0 @ X36))),
% 0.93/1.13      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.93/1.13  thf('3', plain,
% 0.93/1.13      (![X36 : $i]:
% 0.93/1.13         (~ (v1_zfmisc_1 @ X36)
% 0.93/1.13          | (m1_subset_1 @ (sk_B_1 @ X36) @ X36)
% 0.93/1.13          | (v1_xboole_0 @ X36))),
% 0.93/1.13      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.93/1.13  thf(redefinition_k6_domain_1, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.93/1.13       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.93/1.13  thf('4', plain,
% 0.93/1.13      (![X34 : $i, X35 : $i]:
% 0.93/1.13         ((v1_xboole_0 @ X34)
% 0.93/1.13          | ~ (m1_subset_1 @ X35 @ X34)
% 0.93/1.13          | ((k6_domain_1 @ X34 @ X35) = (k1_tarski @ X35)))),
% 0.93/1.13      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.93/1.13  thf('5', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         ((v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (v1_zfmisc_1 @ X0)
% 0.93/1.13          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.93/1.13          | (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['3', '4'])).
% 0.93/1.13  thf('6', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.93/1.13          | ~ (v1_zfmisc_1 @ X0)
% 0.93/1.13          | (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('simplify', [status(thm)], ['5'])).
% 0.93/1.13  thf('7', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.93/1.13          | (v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (v1_zfmisc_1 @ X0)
% 0.93/1.13          | (v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (v1_zfmisc_1 @ X0))),
% 0.93/1.13      inference('sup+', [status(thm)], ['2', '6'])).
% 0.93/1.13  thf('8', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (~ (v1_zfmisc_1 @ X0)
% 0.93/1.13          | (v1_xboole_0 @ X0)
% 0.93/1.13          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.93/1.13      inference('simplify', [status(thm)], ['7'])).
% 0.93/1.13  thf('9', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(l32_xboole_1, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.93/1.13  thf('10', plain,
% 0.93/1.13      (![X16 : $i, X18 : $i]:
% 0.93/1.13         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.93/1.13          | ~ (r1_tarski @ X16 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.93/1.13  thf('11', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.93/1.13  thf(t39_xboole_1, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.93/1.13  thf('12', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.93/1.13           = (k2_xboole_0 @ X27 @ X28))),
% 0.93/1.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.93/1.13  thf('13', plain,
% 0.93/1.13      (((k2_xboole_0 @ sk_B_2 @ k1_xboole_0) = (k2_xboole_0 @ sk_B_2 @ sk_A))),
% 0.93/1.13      inference('sup+', [status(thm)], ['11', '12'])).
% 0.93/1.13  thf(t1_boole, axiom,
% 0.93/1.13    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.93/1.13  thf('14', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.93/1.13      inference('cnf', [status(esa)], [t1_boole])).
% 0.93/1.13  thf('15', plain, (((sk_B_2) = (k2_xboole_0 @ sk_B_2 @ sk_A))),
% 0.93/1.13      inference('demod', [status(thm)], ['13', '14'])).
% 0.93/1.13  thf(t44_zfmisc_1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.93/1.13          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.93/1.13          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.93/1.13  thf('16', plain,
% 0.93/1.13      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.93/1.13         (((X29) = (k1_xboole_0))
% 0.93/1.13          | ((X30) = (k1_xboole_0))
% 0.93/1.13          | ((X29) = (X30))
% 0.93/1.13          | ((k1_tarski @ X31) != (k2_xboole_0 @ X29 @ X30)))),
% 0.93/1.13      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.93/1.13  thf('17', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((k1_tarski @ X0) != (sk_B_2))
% 0.93/1.13          | ((sk_B_2) = (sk_A))
% 0.93/1.13          | ((sk_A) = (k1_xboole_0))
% 0.93/1.13          | ((sk_B_2) = (k1_xboole_0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['15', '16'])).
% 0.93/1.13  thf('18', plain, (((sk_A) != (sk_B_2))),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('19', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((k1_tarski @ X0) != (sk_B_2))
% 0.93/1.13          | ((sk_A) = (k1_xboole_0))
% 0.93/1.13          | ((sk_B_2) = (k1_xboole_0)))),
% 0.93/1.13      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.93/1.13  thf('20', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((X0) != (sk_B_2))
% 0.93/1.13          | (v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (v1_zfmisc_1 @ X0)
% 0.93/1.13          | ((sk_B_2) = (k1_xboole_0))
% 0.93/1.13          | ((sk_A) = (k1_xboole_0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['8', '19'])).
% 0.93/1.13  thf('21', plain,
% 0.93/1.13      ((((sk_A) = (k1_xboole_0))
% 0.93/1.13        | ((sk_B_2) = (k1_xboole_0))
% 0.93/1.13        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.93/1.13        | (v1_xboole_0 @ sk_B_2))),
% 0.93/1.13      inference('simplify', [status(thm)], ['20'])).
% 0.93/1.13  thf('22', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('23', plain,
% 0.93/1.13      ((((sk_A) = (k1_xboole_0))
% 0.93/1.13        | ((sk_B_2) = (k1_xboole_0))
% 0.93/1.13        | (v1_xboole_0 @ sk_B_2))),
% 0.93/1.13      inference('simplify_reflect+', [status(thm)], ['21', '22'])).
% 0.93/1.13  thf('24', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('25', plain, ((((sk_B_2) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.93/1.13      inference('clc', [status(thm)], ['23', '24'])).
% 0.93/1.13  thf(d1_xboole_0, axiom,
% 0.93/1.13    (![A:$i]:
% 0.93/1.13     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.93/1.13  thf('26', plain,
% 0.93/1.13      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.93/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.93/1.13  thf('27', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf(t10_xboole_1, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.93/1.13  thf('28', plain,
% 0.93/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.93/1.13         (~ (r1_tarski @ X19 @ X20)
% 0.93/1.13          | (r1_tarski @ X19 @ (k2_xboole_0 @ X21 @ X20)))),
% 0.93/1.13      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.93/1.13  thf('29', plain,
% 0.93/1.13      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B_2))),
% 0.93/1.13      inference('sup-', [status(thm)], ['27', '28'])).
% 0.93/1.13  thf(d3_tarski, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( r1_tarski @ A @ B ) <=>
% 0.93/1.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.93/1.13  thf('30', plain,
% 0.93/1.13      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.93/1.13         (~ (r2_hidden @ X3 @ X4)
% 0.93/1.13          | (r2_hidden @ X3 @ X5)
% 0.93/1.13          | ~ (r1_tarski @ X4 @ X5))),
% 0.93/1.13      inference('cnf', [status(esa)], [d3_tarski])).
% 0.93/1.13  thf('31', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         ((r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ sk_B_2))
% 0.93/1.13          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.93/1.13      inference('sup-', [status(thm)], ['29', '30'])).
% 0.93/1.13  thf('32', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         ((v1_xboole_0 @ sk_A)
% 0.93/1.13          | (r2_hidden @ (sk_B @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B_2)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['26', '31'])).
% 0.93/1.13  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.93/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.93/1.13  thf('34', plain,
% 0.93/1.13      (![X0 : $i]: (r2_hidden @ (sk_B @ sk_A) @ (k2_xboole_0 @ X0 @ sk_B_2))),
% 0.93/1.13      inference('clc', [status(thm)], ['32', '33'])).
% 0.93/1.13  thf('35', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.93/1.13           = (k2_xboole_0 @ X27 @ X28))),
% 0.93/1.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.93/1.13  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.93/1.13  thf('36', plain, (![X26 : $i]: (r1_tarski @ k1_xboole_0 @ X26)),
% 0.93/1.13      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.93/1.13  thf('37', plain,
% 0.93/1.13      (![X4 : $i, X6 : $i]:
% 0.93/1.13         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.93/1.13      inference('cnf', [status(esa)], [d3_tarski])).
% 0.93/1.13  thf('38', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.93/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.93/1.13  thf('39', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.93/1.13  thf('40', plain,
% 0.93/1.13      (![X16 : $i, X18 : $i]:
% 0.93/1.13         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.93/1.13          | ~ (r1_tarski @ X16 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.93/1.13  thf('41', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ X1) | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.93/1.13  thf('42', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.93/1.13           = (k2_xboole_0 @ X27 @ X28))),
% 0.93/1.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.93/1.13  thf('43', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (((k2_xboole_0 @ X1 @ k1_xboole_0) = (k2_xboole_0 @ X1 @ X0))
% 0.93/1.13          | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('sup+', [status(thm)], ['41', '42'])).
% 0.93/1.13  thf('44', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.93/1.13      inference('cnf', [status(esa)], [t1_boole])).
% 0.93/1.13  thf('45', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (((X1) = (k2_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('demod', [status(thm)], ['43', '44'])).
% 0.93/1.13  thf(d10_xboole_0, axiom,
% 0.93/1.13    (![A:$i,B:$i]:
% 0.93/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.93/1.13  thf('46', plain,
% 0.93/1.13      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.93/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.93/1.13  thf('47', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.93/1.13      inference('simplify', [status(thm)], ['46'])).
% 0.93/1.13  thf('48', plain,
% 0.93/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.93/1.13         (~ (r1_tarski @ X19 @ X20)
% 0.93/1.13          | (r1_tarski @ X19 @ (k2_xboole_0 @ X21 @ X20)))),
% 0.93/1.13      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.93/1.13  thf('49', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['47', '48'])).
% 0.93/1.13  thf('50', plain,
% 0.93/1.13      (![X13 : $i, X15 : $i]:
% 0.93/1.13         (((X13) = (X15))
% 0.93/1.13          | ~ (r1_tarski @ X15 @ X13)
% 0.93/1.13          | ~ (r1_tarski @ X13 @ X15))),
% 0.93/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.93/1.13  thf('51', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.93/1.13          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.93/1.13  thf('52', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (r1_tarski @ X0 @ X1)
% 0.93/1.13          | ~ (v1_xboole_0 @ X1)
% 0.93/1.13          | ((k2_xboole_0 @ X0 @ X1) = (X1)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['45', '51'])).
% 0.93/1.13  thf('53', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['36', '52'])).
% 0.93/1.13  thf('54', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.93/1.13           = (k2_xboole_0 @ X27 @ X28))),
% 0.93/1.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.93/1.13  thf('55', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['47', '48'])).
% 0.93/1.13  thf('56', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.93/1.13  thf('57', plain,
% 0.93/1.13      (![X13 : $i, X15 : $i]:
% 0.93/1.13         (((X13) = (X15))
% 0.93/1.13          | ~ (r1_tarski @ X15 @ X13)
% 0.93/1.13          | ~ (r1_tarski @ X13 @ X15))),
% 0.93/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.93/1.13  thf('58', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['56', '57'])).
% 0.93/1.13  thf('59', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 0.93/1.13          | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['55', '58'])).
% 0.93/1.13  thf('60', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 0.93/1.13          | ((k4_xboole_0 @ X0 @ X1)
% 0.93/1.13              = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.93/1.13      inference('sup-', [status(thm)], ['54', '59'])).
% 0.93/1.13  thf('61', plain,
% 0.93/1.13      (![X27 : $i, X28 : $i]:
% 0.93/1.13         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.93/1.13           = (k2_xboole_0 @ X27 @ X28))),
% 0.93/1.13      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.93/1.13  thf('62', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0))
% 0.93/1.13          | ((k4_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0)))),
% 0.93/1.13      inference('demod', [status(thm)], ['60', '61'])).
% 0.93/1.13  thf('63', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (v1_xboole_0 @ X0)
% 0.93/1.13          | ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.93/1.13              = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['53', '62'])).
% 0.93/1.13  thf('64', plain,
% 0.93/1.13      (![X0 : $i]:
% 0.93/1.13         (((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.93/1.13          | ~ (v1_xboole_0 @ X0))),
% 0.93/1.13      inference('simplify', [status(thm)], ['63'])).
% 0.93/1.13  thf(d5_xboole_0, axiom,
% 0.93/1.13    (![A:$i,B:$i,C:$i]:
% 0.93/1.13     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.93/1.13       ( ![D:$i]:
% 0.93/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.93/1.13           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.93/1.13  thf('65', plain,
% 0.93/1.13      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.93/1.13         (~ (r2_hidden @ X11 @ X10)
% 0.93/1.13          | (r2_hidden @ X11 @ X8)
% 0.93/1.13          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.93/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.93/1.13  thf('66', plain,
% 0.93/1.13      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.93/1.13         ((r2_hidden @ X11 @ X8)
% 0.93/1.13          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.93/1.13      inference('simplify', [status(thm)], ['65'])).
% 0.93/1.13  thf('67', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.93/1.13          | ~ (v1_xboole_0 @ X0)
% 0.93/1.13          | (r2_hidden @ X1 @ X0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['64', '66'])).
% 0.93/1.13  thf('68', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.93/1.13      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.93/1.13  thf('69', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (v1_xboole_0 @ X0)
% 0.93/1.13          | ~ (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.93/1.13      inference('clc', [status(thm)], ['67', '68'])).
% 0.93/1.13  thf('70', plain,
% 0.93/1.13      (![X0 : $i, X1 : $i]:
% 0.93/1.13         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 0.93/1.13          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['35', '69'])).
% 0.93/1.13  thf('71', plain, (~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_2 @ k1_xboole_0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['34', '70'])).
% 0.93/1.13  thf('72', plain,
% 0.93/1.13      ((~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_2 @ sk_B_2))
% 0.93/1.13        | ((sk_A) = (k1_xboole_0)))),
% 0.93/1.13      inference('sup-', [status(thm)], ['25', '71'])).
% 0.93/1.13  thf('73', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.93/1.13      inference('simplify', [status(thm)], ['46'])).
% 0.93/1.13  thf('74', plain,
% 0.93/1.13      (![X16 : $i, X18 : $i]:
% 0.93/1.13         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.93/1.13          | ~ (r1_tarski @ X16 @ X18))),
% 0.93/1.13      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.93/1.13  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.93/1.13      inference('sup-', [status(thm)], ['73', '74'])).
% 0.93/1.13  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.93/1.13      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.93/1.13  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.93/1.13      inference('demod', [status(thm)], ['72', '75', '76'])).
% 0.93/1.13  thf('78', plain, ((v1_xboole_0 @ sk_A)),
% 0.93/1.13      inference('demod', [status(thm)], ['1', '77'])).
% 0.93/1.13  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.93/1.13  
% 0.93/1.13  % SZS output end Refutation
% 0.93/1.13  
% 0.93/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
