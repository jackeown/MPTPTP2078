%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cep4ZS4c6x

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:02 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 494 expanded)
%              Number of leaves         :   44 ( 182 expanded)
%              Depth                    :   21
%              Number of atoms          :  820 (3170 expanded)
%              Number of equality atoms :   49 ( 199 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X28 @ X26 ) @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) @ X20 )
        = ( k7_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X31 ) @ ( sk_C_3 @ X31 ) ) @ X31 )
      | ( X31 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X21: $i] :
      ( ( ( k7_relat_1 @ X21 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X35: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29
        = ( k7_relat_1 @ X29 @ X30 ) )
      | ~ ( v4_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k6_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('20',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X28 @ X26 ) @ X27 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('30',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ X25 @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('42',plain,
    ( k1_xboole_0
    = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X12 @ X13 ) @ ( sk_D_1 @ X12 @ X13 ) ) @ X13 )
      | ( r1_tarski @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('48',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) )
        = ( k9_relat_1 @ X22 @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','52','53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('61',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('65',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ X25 @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','32'])).

thf('69',plain,
    ( ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( v1_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('71',plain,(
    v1_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ) ),
    inference(demod,[status(thm)],['8','72'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v2_funct_1 @ X37 )
      | ( ( k9_relat_1 @ X37 @ ( k3_xboole_0 @ X38 @ X39 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X37 @ X38 ) @ ( k9_relat_1 @ X37 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B_2 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B_2 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_4 @ sk_A ) @ ( k9_relat_1 @ sk_C_4 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C_4 )
    | ~ ( v2_funct_1 @ sk_C_4 )
    | ~ ( v1_funct_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['82','83','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cep4ZS4c6x
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 211 iterations in 0.147s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.44/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.44/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.44/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.44/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(sk_C_3_type, type, sk_C_3: $i > $i).
% 0.44/0.61  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.44/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.61  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.44/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.44/0.61  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.44/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.61  thf(t125_funct_1, conjecture,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.61       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.44/0.61         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.61          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.44/0.61            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.44/0.61  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B_2)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(t207_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ C ) =>
% 0.44/0.61       ( ( r1_xboole_0 @ A @ B ) =>
% 0.44/0.61         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X26 @ X27)
% 0.44/0.61          | ~ (v1_relat_1 @ X28)
% 0.44/0.61          | ((k7_relat_1 @ (k7_relat_1 @ X28 @ X26) @ X27) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B_2) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.61  thf(t100_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ C ) =>
% 0.44/0.61       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.44/0.61         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.44/0.61  thf('3', plain,
% 0.44/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.61         (((k7_relat_1 @ (k7_relat_1 @ X18 @ X19) @ X20)
% 0.44/0.61            = (k7_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20)))
% 0.44/0.61          | ~ (v1_relat_1 @ X18))),
% 0.44/0.61      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k1_xboole_0) = (k7_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2)))
% 0.44/0.61          | ~ (v1_relat_1 @ X0)
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['2', '3'])).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | ((k1_xboole_0) = (k7_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.61  thf(t148_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ B ) =>
% 0.44/0.61       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i]:
% 0.44/0.61         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 0.44/0.61          | ~ (v1_relat_1 @ X22))),
% 0.44/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.61  thf('7', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_relat_1 @ k1_xboole_0)
% 0.44/0.61            = (k9_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2)))
% 0.44/0.61          | ~ (v1_relat_1 @ X0)
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.44/0.61  thf('8', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | ((k2_relat_1 @ k1_xboole_0)
% 0.44/0.61              = (k9_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))))),
% 0.44/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.44/0.61  thf(t56_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.44/0.61         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.61  thf('9', plain,
% 0.44/0.61      (![X31 : $i]:
% 0.44/0.61         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X31) @ (sk_C_3 @ X31)) @ X31)
% 0.44/0.61          | ((X31) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X31))),
% 0.44/0.61      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.44/0.61  thf(t110_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.61  thf('10', plain,
% 0.44/0.61      (![X21 : $i]:
% 0.44/0.61         (((k7_relat_1 @ X21 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X21))),
% 0.44/0.61      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.44/0.61  thf(fc24_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.44/0.61       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.44/0.61       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.44/0.61  thf('11', plain, (![X35 : $i]: (v4_relat_1 @ (k6_relat_1 @ X35) @ X35)),
% 0.44/0.61      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.44/0.61  thf(t209_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.61       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.44/0.61  thf('12', plain,
% 0.44/0.61      (![X29 : $i, X30 : $i]:
% 0.44/0.61         (((X29) = (k7_relat_1 @ X29 @ X30))
% 0.44/0.61          | ~ (v4_relat_1 @ X29 @ X30)
% 0.44/0.61          | ~ (v1_relat_1 @ X29))),
% 0.44/0.61      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.44/0.61  thf('13', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.44/0.61          | ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.61  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.44/0.61  thf('14', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.61  thf('15', plain,
% 0.44/0.61      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      ((((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61        | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['10', '15'])).
% 0.44/0.61  thf('17', plain, (![X17 : $i]: (v1_relat_1 @ (k6_relat_1 @ X17))),
% 0.44/0.61      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.44/0.61  thf('18', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X0 : $i]: ((k6_relat_1 @ X0) = (k7_relat_1 @ (k6_relat_1 @ X0) @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.61  thf('20', plain,
% 0.44/0.61      (((k6_relat_1 @ k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['18', '19'])).
% 0.44/0.61  thf('21', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.61  thf('23', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.44/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.44/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.44/0.61  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ X26 @ X27)
% 0.44/0.61          | ~ (v1_relat_1 @ X28)
% 0.44/0.61          | ((k7_relat_1 @ (k7_relat_1 @ X28 @ X26) @ X27) = (k1_xboole_0)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ X1))),
% 0.44/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['22', '27'])).
% 0.44/0.61  thf(d1_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) <=>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ~( ( r2_hidden @ B @ A ) & 
% 0.44/0.61              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.44/0.61  thf('29', plain,
% 0.44/0.61      (![X9 : $i]: ((v1_relat_1 @ X9) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.44/0.61  thf('30', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.44/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.61  thf(l24_zfmisc_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.44/0.61  thf('31', plain,
% 0.44/0.61      (![X5 : $i, X6 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X5) @ X6) | ~ (r2_hidden @ X5 @ X6))),
% 0.44/0.61      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.44/0.61  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.61  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('34', plain,
% 0.44/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '33'])).
% 0.44/0.61  thf('35', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i]:
% 0.44/0.61         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 0.44/0.61          | ~ (v1_relat_1 @ X22))),
% 0.44/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.61  thf(t19_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ B ) =>
% 0.44/0.61       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.44/0.61            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.44/0.61  thf('36', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_C_2 @ X24) @ (k1_relat_1 @ X24))
% 0.44/0.61          | ~ (r2_hidden @ X25 @ (k2_relat_1 @ X24))
% 0.44/0.61          | ~ (v1_relat_1 @ X24))),
% 0.44/0.61      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.44/0.61  thf('37', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.44/0.61          | ~ (v1_relat_1 @ X1)
% 0.44/0.61          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.44/0.61          | (r2_hidden @ (sk_C_2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.44/0.61             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.44/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.61  thf('38', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.61          | (r2_hidden @ (sk_C_2 @ (k7_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.44/0.61             (k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)))
% 0.44/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.61          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ k1_xboole_0 @ X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['34', '37'])).
% 0.44/0.61  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('40', plain,
% 0.44/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '33'])).
% 0.44/0.61  thf('41', plain,
% 0.44/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '33'])).
% 0.44/0.61  thf('42', plain,
% 0.44/0.61      (((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['20', '21'])).
% 0.44/0.61  thf(d3_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ![B:$i]:
% 0.44/0.61         ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.61           ( ![C:$i,D:$i]:
% 0.44/0.61             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.44/0.61               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.44/0.61  thf('43', plain,
% 0.44/0.61      (![X12 : $i, X13 : $i]:
% 0.44/0.61         ((r2_hidden @ 
% 0.44/0.61           (k4_tarski @ (sk_C_1 @ X12 @ X13) @ (sk_D_1 @ X12 @ X13)) @ X13)
% 0.44/0.61          | (r1_tarski @ X13 @ X12)
% 0.44/0.61          | ~ (v1_relat_1 @ X13))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.44/0.61  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.61  thf('45', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ k1_xboole_0) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.61  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.61  thf(t91_relat_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ B ) =>
% 0.44/0.61       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.61         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.44/0.61  thf('48', plain,
% 0.44/0.61      (![X32 : $i, X33 : $i]:
% 0.44/0.61         (~ (r1_tarski @ X32 @ (k1_relat_1 @ X33))
% 0.44/0.61          | ((k1_relat_1 @ (k7_relat_1 @ X33 @ X32)) = (X32))
% 0.44/0.61          | ~ (v1_relat_1 @ X33))),
% 0.44/0.61      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.44/0.61  thf('49', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.61  thf('50', plain,
% 0.44/0.61      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.44/0.61        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['42', '49'])).
% 0.44/0.61  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.61  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('54', plain,
% 0.44/0.61      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['28', '33'])).
% 0.44/0.61  thf('55', plain,
% 0.44/0.61      (![X22 : $i, X23 : $i]:
% 0.44/0.61         (((k2_relat_1 @ (k7_relat_1 @ X22 @ X23)) = (k9_relat_1 @ X22 @ X23))
% 0.44/0.61          | ~ (v1_relat_1 @ X22))),
% 0.44/0.61      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.61  thf('56', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.44/0.61          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.61  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('58', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.61  thf('59', plain,
% 0.44/0.61      (![X1 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.44/0.61          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)],
% 0.44/0.61                ['38', '39', '40', '41', '52', '53', '58'])).
% 0.44/0.61  thf('60', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.61  thf('61', plain,
% 0.44/0.61      (![X1 : $i]: ~ (r2_hidden @ X1 @ (k2_relat_1 @ k1_xboole_0))),
% 0.44/0.61      inference('clc', [status(thm)], ['59', '60'])).
% 0.44/0.61  thf('62', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ (k2_relat_1 @ k1_xboole_0))
% 0.44/0.61        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['9', '61'])).
% 0.44/0.61  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.61  thf('64', plain,
% 0.44/0.61      (![X9 : $i]: ((v1_relat_1 @ X9) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.44/0.61      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.44/0.61  thf('65', plain,
% 0.44/0.61      (![X24 : $i, X25 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_C_2 @ X24) @ (k1_relat_1 @ X24))
% 0.44/0.61          | ~ (r2_hidden @ X25 @ (k2_relat_1 @ X24))
% 0.44/0.61          | ~ (v1_relat_1 @ X24))),
% 0.44/0.61      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.44/0.61  thf('66', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((v1_relat_1 @ (k2_relat_1 @ X0))
% 0.44/0.61          | ~ (v1_relat_1 @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.44/0.61  thf('67', plain,
% 0.44/0.61      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.44/0.61        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.44/0.61        | (v1_relat_1 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.44/0.61      inference('sup+', [status(thm)], ['63', '66'])).
% 0.44/0.61  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['29', '32'])).
% 0.44/0.61  thf('69', plain,
% 0.44/0.61      (((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)
% 0.44/0.61        | (v1_relat_1 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.44/0.61      inference('demod', [status(thm)], ['67', '68'])).
% 0.44/0.61  thf('70', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.61  thf('71', plain, ((v1_relat_1 @ (k2_relat_1 @ k1_xboole_0))),
% 0.44/0.61      inference('clc', [status(thm)], ['69', '70'])).
% 0.44/0.61  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.61      inference('demod', [status(thm)], ['62', '71'])).
% 0.44/0.61  thf('73', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))))),
% 0.44/0.61      inference('demod', [status(thm)], ['8', '72'])).
% 0.44/0.61  thf(t121_funct_1, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.61       ( ( v2_funct_1 @ C ) =>
% 0.44/0.61         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.44/0.61           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.44/0.61  thf('74', plain,
% 0.44/0.61      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.44/0.61         (~ (v2_funct_1 @ X37)
% 0.44/0.61          | ((k9_relat_1 @ X37 @ (k3_xboole_0 @ X38 @ X39))
% 0.44/0.61              = (k3_xboole_0 @ (k9_relat_1 @ X37 @ X38) @ 
% 0.44/0.61                 (k9_relat_1 @ X37 @ X39)))
% 0.44/0.61          | ~ (v1_funct_1 @ X37)
% 0.44/0.61          | ~ (v1_relat_1 @ X37))),
% 0.44/0.61      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.44/0.61  thf(t75_xboole_1, axiom,
% 0.44/0.61    (![A:$i,B:$i]:
% 0.44/0.61     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.61          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.44/0.61  thf('75', plain,
% 0.44/0.61      (![X3 : $i, X4 : $i]:
% 0.44/0.61         ((r1_xboole_0 @ X3 @ X4)
% 0.44/0.61          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ X4))),
% 0.44/0.61      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.44/0.61  thf('76', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.44/0.61             (k9_relat_1 @ X2 @ X0))
% 0.44/0.61          | ~ (v1_relat_1 @ X2)
% 0.44/0.61          | ~ (v1_funct_1 @ X2)
% 0.44/0.61          | ~ (v2_funct_1 @ X2)
% 0.44/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['74', '75'])).
% 0.44/0.61  thf('77', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (r1_xboole_0 @ k1_xboole_0 @ (k9_relat_1 @ X0 @ sk_B_2))
% 0.44/0.61          | ~ (v1_relat_1 @ X0)
% 0.44/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.44/0.61             (k9_relat_1 @ X0 @ sk_B_2))
% 0.44/0.61          | ~ (v2_funct_1 @ X0)
% 0.44/0.61          | ~ (v1_funct_1 @ X0)
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['73', '76'])).
% 0.44/0.61  thf('78', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.44/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.61  thf('79', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X0)
% 0.44/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.44/0.61             (k9_relat_1 @ X0 @ sk_B_2))
% 0.44/0.61          | ~ (v2_funct_1 @ X0)
% 0.44/0.61          | ~ (v1_funct_1 @ X0)
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['77', '78'])).
% 0.44/0.61  thf('80', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         (~ (v1_funct_1 @ X0)
% 0.44/0.61          | ~ (v2_funct_1 @ X0)
% 0.44/0.61          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.44/0.61             (k9_relat_1 @ X0 @ sk_B_2))
% 0.44/0.61          | ~ (v1_relat_1 @ X0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['79'])).
% 0.44/0.61  thf('81', plain,
% 0.44/0.61      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_4 @ sk_A) @ 
% 0.44/0.61          (k9_relat_1 @ sk_C_4 @ sk_B_2))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('82', plain,
% 0.44/0.61      ((~ (v1_relat_1 @ sk_C_4)
% 0.44/0.61        | ~ (v2_funct_1 @ sk_C_4)
% 0.44/0.61        | ~ (v1_funct_1 @ sk_C_4))),
% 0.44/0.61      inference('sup-', [status(thm)], ['80', '81'])).
% 0.44/0.61  thf('83', plain, ((v1_relat_1 @ sk_C_4)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('84', plain, ((v2_funct_1 @ sk_C_4)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('85', plain, ((v1_funct_1 @ sk_C_4)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('86', plain, ($false),
% 0.44/0.61      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
