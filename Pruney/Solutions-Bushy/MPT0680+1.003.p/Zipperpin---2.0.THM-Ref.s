%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0680+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CMKJCApjWo

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 184 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   21
%              Number of atoms          :  989 (2421 expanded)
%              Number of equality atoms :   74 ( 164 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
        = ( k1_tarski @ X10 ) )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k6_subset_1 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X11 ) )
        = ( k1_tarski @ X10 ) )
      | ( X10 = X11 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ X13 @ X14 ) )
      = ( k6_subset_1 @ ( k9_relat_1 @ sk_A @ X13 ) @ ( k9_relat_1 @ sk_A @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
        = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X1 ) @ ( k11_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
        = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k11_relat_1 @ sk_A @ X1 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

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

thf('14',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_B @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k11_relat_1 @ X8 @ X7 )
        = ( k1_tarski @ ( k1_funct_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( ( k1_funct_1 @ X2 @ ( sk_B @ X2 ) )
        = ( k1_funct_1 @ X2 @ ( sk_C @ X2 ) ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 ) @ ( k1_relat_1 @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k11_relat_1 @ X8 @ X7 )
        = ( k1_tarski @ ( k1_funct_1 @ X8 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X10 != X9 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X10 ) @ ( k1_tarski @ X9 ) )
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X9 ) )
     != ( k1_tarski @ X9 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( k6_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X9 ) )
     != ( k1_tarski @ X9 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k1_tarski @ ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) )
       != ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ ( sk_C @ X0 ) )
        = ( k11_relat_1 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_C @ sk_A ) ) @ X0 ) )
        = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ ( sk_B @ sk_A ) ) @ ( k9_relat_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      = ( k6_subset_1 @ ( k11_relat_1 @ sk_A @ X0 ) @ ( k9_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_C @ sk_A ) ) @ X0 ) )
        = ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ X0 ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_C @ sk_A ) ) @ X0 ) )
      = ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
    = ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('57',plain,
    ( ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_C @ sk_A ) ) )
    = ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) )
      = ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) )
    = ( k9_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) )
     != ( k11_relat_1 @ sk_A @ ( sk_C @ sk_A ) ) )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['41','60','61','62'])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( sk_C @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( sk_B @ sk_A )
    = ( sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i] :
      ( ( ( sk_B @ X2 )
       != ( sk_C @ X2 ) )
      | ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('68',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( sk_B @ sk_A )
     != ( sk_B @ sk_A ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).


%------------------------------------------------------------------------------
