%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0866+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7l3NEyiUfk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:03 EST 2020

% Result     : Theorem 38.51s
% Output     : Refutation 38.60s
% Verified   : 
% Statistics : Number of formulae       :   48 (  59 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  244 ( 367 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_93_type,type,(
    sk_C_93: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_73_type,type,(
    sk_B_73: $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t24_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C @ ( k2_mcart_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )
               => ( C
                  = ( k4_tarski @ ( k1_mcart_1 @ C @ ( k2_mcart_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) )
    | ( r2_hidden @ ( sk_C_93 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ ( A @ B ) )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A @ ( k2_mcart_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X3892: $i,X3893: $i] :
      ( ( X3892
        = ( k4_tarski @ ( k1_mcart_1 @ X3892 @ ( k2_mcart_1 @ X3892 ) ) ) )
      | ~ ( v1_relat_1 @ X3893 )
      | ~ ( r2_hidden @ ( X3892 @ X3893 ) ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) )
    | ( sk_C_93
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) )
    | ( sk_C_93
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_C_93
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C_93 @ ( k2_mcart_1 @ sk_C_93 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_73 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X1103: $i,X1104: $i] :
      ( ( X1103 = k1_xboole_0 )
      | ( X1104 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1104 @ X1103 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X1103: $i,X1104: $i] :
      ( ( X1103 = o_0_0_xboole_0 )
      | ( X1104 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1104 @ X1103 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 )
    | ( sk_B_73 = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_B_73 = o_0_0_xboole_0 )
    | ( sk_A_14 = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    sk_A_14 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    sk_A_14 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B_73 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    sk_B_73 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','22','25'])).

%------------------------------------------------------------------------------
