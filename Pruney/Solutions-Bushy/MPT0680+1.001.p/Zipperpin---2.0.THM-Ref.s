%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0680+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CNnQsKJ4U1

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:19 EST 2020

% Result     : Theorem 14.43s
% Output     : Refutation 14.46s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 118 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   21
%              Number of atoms          :  748 (1494 expanded)
%              Number of equality atoms :   60 ( 106 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t124_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i,C: $i] :
            ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) )
            = ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ! [B: $i,C: $i] :
              ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) )
              = ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('3',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k11_relat_1 @ X14 @ X13 )
        = ( k1_tarski @ ( k1_funct_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k11_relat_1 @ X2 @ X3 )
        = ( k9_relat_1 @ X2 @ ( k1_tarski @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ X30 @ X31 ) )
      = ( k6_subset_1 @ ( k9_relat_1 @ sk_A @ X30 ) @ ( k9_relat_1 @ sk_A @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ X30 @ X31 ) )
      = ( k4_xboole_0 @ ( k9_relat_1 @ sk_A @ X30 ) @ ( k9_relat_1 @ sk_A @ X31 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
        = ( k4_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k4_xboole_0 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ X1 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('24',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( ( k11_relat_1 @ X14 @ X13 )
        = ( k1_tarski @ ( k1_funct_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ( v2_funct_1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) )
    | ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ( ( sk_C @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C @ sk_A )
    = ( sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).


%------------------------------------------------------------------------------
