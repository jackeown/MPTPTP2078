%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xl6exUA0tg

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 740 expanded)
%              Number of leaves         :   35 ( 251 expanded)
%              Depth                    :   25
%              Number of atoms          : 1678 (8065 expanded)
%              Number of equality atoms :  194 ( 939 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X8 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = o_0_0_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X8 )
      | ( X9 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('6',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['20','23'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('36',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k1_relat_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('40',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_zfmisc_1 @ X13 @ X14 @ X15 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('49',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k4_tarski @ ( k1_mcart_1 @ X19 ) @ ( k2_mcart_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_mcart_1 @ X10 @ X11 @ X12 )
      = ( k4_tarski @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('65',plain,
    ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X26 @ X25 @ X27 ) )
      | ( sk_D = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = o_0_0_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('76',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('77',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('78',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('79',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X21 = o_0_0_xboole_0 )
      | ( X22 = o_0_0_xboole_0 )
      | ( ( k7_mcart_1 @ X21 @ X22 @ X24 @ X23 )
        = ( k2_mcart_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k3_zfmisc_1 @ X21 @ X22 @ X24 ) )
      | ( X24 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('83',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('86',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('88',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['80','83','86','87'])).

thf('89',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['73','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['72','89'])).

thf('91',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('94',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X2 @ X1 ) )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ ( k1_relat_1 @ X0 ) )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X5: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('108',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('110',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('114',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('116',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X26 @ X25 @ X27 ) )
      | ( sk_D = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['105','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['73','88'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('127',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('130',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('132',plain,
    ( ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('135',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( o_0_0_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['96','135'])).

thf('137',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    sk_C != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('139',plain,
    ( o_0_0_xboole_0
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = o_0_0_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
        = X8 )
      | ( X9 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('141',plain,
    ( ( ( k1_relat_1 @ o_0_0_xboole_0 )
      = sk_A )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['133','134'])).

thf('143',plain,
    ( ( o_0_0_xboole_0 = sk_A )
    | ( sk_B = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 = sk_A ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('146',plain,(
    sk_B != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('147',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['144','145','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xl6exUA0tg
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:53:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.58  % Solved by: fo/fo7.sh
% 0.22/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.58  % done 242 iterations in 0.118s
% 0.22/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.58  % SZS output start Refutation
% 0.22/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.58  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.58  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.58  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.22/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.58  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.58  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.58  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.58  thf(d3_zfmisc_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.58       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.58  thf('0', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.58         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.22/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.58  thf(t195_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.58          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.22/0.58               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.22/0.58  thf('1', plain,
% 0.22/0.58      (![X8 : $i, X9 : $i]:
% 0.22/0.58         (((X8) = (k1_xboole_0))
% 0.22/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X8))
% 0.22/0.58          | ((X9) = (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.22/0.58  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.22/0.58  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('3', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('4', plain,
% 0.22/0.58      (![X8 : $i, X9 : $i]:
% 0.22/0.58         (((X8) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X8))
% 0.22/0.58          | ((X9) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.22/0.58  thf('5', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.58            = (k2_zfmisc_1 @ X2 @ X1))
% 0.22/0.58          | ((X0) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['0', '4'])).
% 0.22/0.58  thf(t71_mcart_1, conjecture,
% 0.22/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.58       ( ( ![F:$i]:
% 0.22/0.58           ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.58             ( ![G:$i]:
% 0.22/0.58               ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.58                 ( ![H:$i]:
% 0.22/0.58                   ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.58                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.58                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.22/0.58         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.22/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.58    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.58        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.58          ( ( ![F:$i]:
% 0.22/0.58              ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.58                ( ![G:$i]:
% 0.22/0.58                  ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.58                    ( ![H:$i]:
% 0.22/0.58                      ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.58                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.58                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.22/0.58            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.58              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.22/0.58    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.22/0.58  thf('6', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(t2_subset, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.58  thf('7', plain,
% 0.22/0.58      (![X3 : $i, X4 : $i]:
% 0.22/0.58         ((r2_hidden @ X3 @ X4)
% 0.22/0.58          | (v1_xboole_0 @ X4)
% 0.22/0.58          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.22/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.58  thf('8', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.58  thf('9', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.58         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.22/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.58  thf(t10_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.58       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.58         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.58  thf('10', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.58         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.22/0.58          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.58  thf('11', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.58          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.58  thf('12', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.58  thf(fc10_relat_1, axiom,
% 0.22/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.22/0.58  thf('13', plain,
% 0.22/0.58      (![X5 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.58  thf(l13_xboole_0, axiom,
% 0.22/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.58  thf('14', plain,
% 0.22/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.58  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('16', plain,
% 0.22/0.58      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('17', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.58  thf('18', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['12', '17'])).
% 0.22/0.58  thf('19', plain,
% 0.22/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('sup+', [status(thm)], ['5', '18'])).
% 0.22/0.58  thf('20', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.58  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('22', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('23', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('24', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['20', '23'])).
% 0.22/0.58  thf(t1_subset, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.58  thf('25', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('26', plain,
% 0.22/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.58  thf('27', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.58            = (k2_zfmisc_1 @ X2 @ X1))
% 0.22/0.58          | ((X0) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['0', '4'])).
% 0.22/0.58  thf('28', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.58  thf(t23_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]:
% 0.22/0.58     ( ( v1_relat_1 @ B ) =>
% 0.22/0.58       ( ( r2_hidden @ A @ B ) =>
% 0.22/0.58         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.22/0.58  thf('29', plain,
% 0.22/0.58      (![X19 : $i, X20 : $i]:
% 0.22/0.58         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 0.22/0.58          | ~ (v1_relat_1 @ X20)
% 0.22/0.58          | ~ (r2_hidden @ X19 @ X20))),
% 0.22/0.58      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.22/0.58  thf('30', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ~ (v1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.58  thf('31', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.58         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.22/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.58  thf(fc6_relat_1, axiom,
% 0.22/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.58  thf('32', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.58  thf('33', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (v1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))),
% 0.22/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.22/0.58  thf('34', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.22/0.58      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.58  thf('35', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.58  thf('36', plain,
% 0.22/0.58      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.22/0.58        | ((k1_relat_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.58  thf('37', plain,
% 0.22/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.22/0.58      inference('sup+', [status(thm)], ['27', '36'])).
% 0.22/0.58  thf('38', plain,
% 0.22/0.58      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.58  thf('39', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('40', plain,
% 0.22/0.58      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.22/0.58  thf('41', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.58  thf('42', plain,
% 0.22/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.58         ((k3_zfmisc_1 @ X13 @ X14 @ X15)
% 0.22/0.58           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14) @ X15))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.58  thf('43', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.22/0.58          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.58  thf('44', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.58         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.58          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.58  thf('45', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['41', '44'])).
% 0.22/0.58  thf('46', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.58         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.22/0.58          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.58  thf('47', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.58  thf('48', plain,
% 0.22/0.58      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('49', plain,
% 0.22/0.58      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.58  thf('50', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('51', plain,
% 0.22/0.58      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.58  thf('52', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['41', '44'])).
% 0.22/0.58  thf('53', plain,
% 0.22/0.58      (![X19 : $i, X20 : $i]:
% 0.22/0.58         (((X19) = (k4_tarski @ (k1_mcart_1 @ X19) @ (k2_mcart_1 @ X19)))
% 0.22/0.58          | ~ (v1_relat_1 @ X20)
% 0.22/0.58          | ~ (r2_hidden @ X19 @ X20))),
% 0.22/0.58      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.22/0.58  thf('54', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.58        | ((k1_mcart_1 @ sk_E)
% 0.22/0.58            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.22/0.58               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.22/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.58  thf('55', plain,
% 0.22/0.58      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.58  thf('56', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((k1_mcart_1 @ sk_E)
% 0.22/0.58            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.22/0.58               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 0.22/0.58      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.58  thf(d3_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.22/0.58  thf('57', plain,
% 0.22/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.58         ((k3_mcart_1 @ X10 @ X11 @ X12)
% 0.22/0.58           = (k4_tarski @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.22/0.58      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.22/0.58  thf('58', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.22/0.58            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.22/0.58            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.58  thf('59', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['41', '44'])).
% 0.22/0.58  thf('60', plain,
% 0.22/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.58         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.22/0.58          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.58  thf('61', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.58  thf('62', plain,
% 0.22/0.58      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('63', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.58  thf('64', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('65', plain,
% 0.22/0.58      ((((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.58  thf('66', plain,
% 0.22/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.58         (~ (m1_subset_1 @ X25 @ sk_B)
% 0.22/0.58          | ((sk_E) != (k3_mcart_1 @ X26 @ X25 @ X27))
% 0.22/0.58          | ((sk_D) = (X27))
% 0.22/0.58          | ~ (m1_subset_1 @ X27 @ sk_C)
% 0.22/0.58          | ~ (m1_subset_1 @ X26 @ sk_A))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('67', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.58          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.22/0.58          | ((sk_D) = (X1))
% 0.22/0.58          | ((sk_E)
% 0.22/0.58              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.58  thf('68', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.22/0.58          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['58', '67'])).
% 0.22/0.58  thf('69', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['51', '68'])).
% 0.22/0.58  thf('70', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['69'])).
% 0.22/0.58  thf('71', plain,
% 0.22/0.58      ((((sk_E) != (sk_E))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.22/0.58        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['40', '70'])).
% 0.22/0.58  thf('72', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['71'])).
% 0.22/0.58  thf('73', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('74', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf(t50_mcart_1, axiom,
% 0.22/0.58    (![A:$i,B:$i,C:$i]:
% 0.22/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.58          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.58          ( ~( ![D:$i]:
% 0.22/0.58               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.58                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.58                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.58                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.58                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.58                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.22/0.58  thf('75', plain,
% 0.22/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.58         (((X21) = (k1_xboole_0))
% 0.22/0.58          | ((X22) = (k1_xboole_0))
% 0.22/0.58          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.22/0.58          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.22/0.58          | ((X24) = (k1_xboole_0)))),
% 0.22/0.58      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.58  thf('76', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('77', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('78', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('79', plain,
% 0.22/0.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.58         (((X21) = (o_0_0_xboole_0))
% 0.22/0.58          | ((X22) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k7_mcart_1 @ X21 @ X22 @ X24 @ X23) = (k2_mcart_1 @ X23))
% 0.22/0.58          | ~ (m1_subset_1 @ X23 @ (k3_zfmisc_1 @ X21 @ X22 @ X24))
% 0.22/0.58          | ((X24) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.22/0.58  thf('80', plain,
% 0.22/0.58      ((((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.22/0.58        | ((sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['74', '79'])).
% 0.22/0.58  thf('81', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('82', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('83', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.58  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('85', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.22/0.58  thf('86', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.58  thf('87', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('88', plain,
% 0.22/0.58      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['80', '83', '86', '87'])).
% 0.22/0.58  thf('89', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.22/0.58      inference('demod', [status(thm)], ['73', '88'])).
% 0.22/0.58  thf('90', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['72', '89'])).
% 0.22/0.58  thf('91', plain,
% 0.22/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['26', '90'])).
% 0.22/0.58  thf('92', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['91'])).
% 0.22/0.58  thf('93', plain,
% 0.22/0.58      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.58      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.58  thf('94', plain,
% 0.22/0.58      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('clc', [status(thm)], ['92', '93'])).
% 0.22/0.58  thf('95', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.58         (((k1_relat_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.58            = (k2_zfmisc_1 @ X2 @ X1))
% 0.22/0.58          | ((X0) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k2_zfmisc_1 @ X2 @ X1) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['0', '4'])).
% 0.22/0.58  thf('96', plain,
% 0.22/0.58      ((((k1_relat_1 @ o_0_0_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['94', '95'])).
% 0.22/0.58  thf('97', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 0.22/0.58      inference('demod', [status(thm)], ['30', '33'])).
% 0.22/0.58  thf('98', plain,
% 0.22/0.58      (![X5 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.58  thf('99', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.58  thf('100', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ X0)
% 0.22/0.58          | ((k1_relat_1 @ (k1_relat_1 @ X0)) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.22/0.58  thf('101', plain,
% 0.22/0.58      (![X5 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.58  thf('102', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58          | ~ (v1_xboole_0 @ X0)
% 0.22/0.58          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['100', '101'])).
% 0.22/0.58  thf('103', plain,
% 0.22/0.58      (![X5 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X5)) | ~ (v1_xboole_0 @ X5))),
% 0.22/0.58      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.22/0.58  thf('104', plain,
% 0.22/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.58  thf('105', plain,
% 0.22/0.58      ((((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['97', '104'])).
% 0.22/0.58  thf('106', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.58  thf('107', plain,
% 0.22/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.58  thf('108', plain,
% 0.22/0.58      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.58  thf('109', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('110', plain,
% 0.22/0.58      (((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.22/0.58      inference('sup-', [status(thm)], ['108', '109'])).
% 0.22/0.58  thf('111', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.22/0.58            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 0.22/0.58            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.58  thf('112', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.58  thf('113', plain,
% 0.22/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.58  thf('114', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['112', '113'])).
% 0.22/0.58  thf('115', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('116', plain,
% 0.22/0.58      (((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.22/0.58      inference('sup-', [status(thm)], ['114', '115'])).
% 0.22/0.58  thf('117', plain,
% 0.22/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.58         (~ (m1_subset_1 @ X25 @ sk_B)
% 0.22/0.58          | ((sk_E) != (k3_mcart_1 @ X26 @ X25 @ X27))
% 0.22/0.58          | ((sk_D) = (X27))
% 0.22/0.58          | ~ (m1_subset_1 @ X27 @ sk_C)
% 0.22/0.58          | ~ (m1_subset_1 @ X26 @ sk_A))),
% 0.22/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.58  thf('118', plain,
% 0.22/0.58      (![X0 : $i, X1 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.58          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.22/0.58          | ((sk_D) = (X1))
% 0.22/0.58          | ((sk_E)
% 0.22/0.58              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['116', '117'])).
% 0.22/0.58  thf('119', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.22/0.58          | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['111', '118'])).
% 0.22/0.58  thf('120', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         ((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58          | (v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['110', '119'])).
% 0.22/0.58  thf('121', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 0.22/0.58          | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58          | ((sk_D) = (X0))
% 0.22/0.58          | ~ (m1_subset_1 @ X0 @ sk_C)
% 0.22/0.58          | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('simplify', [status(thm)], ['120'])).
% 0.22/0.58  thf('122', plain,
% 0.22/0.58      ((((sk_E) != (sk_E))
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.22/0.58        | (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['105', '121'])).
% 0.22/0.58  thf('123', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('simplify', [status(thm)], ['122'])).
% 0.22/0.58  thf('124', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.22/0.58      inference('demod', [status(thm)], ['73', '88'])).
% 0.22/0.58  thf('125', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['123', '124'])).
% 0.22/0.58  thf('126', plain,
% 0.22/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.58  thf('127', plain,
% 0.22/0.58      (((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('clc', [status(thm)], ['125', '126'])).
% 0.22/0.58  thf('128', plain,
% 0.22/0.58      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.58        | (r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.58  thf('129', plain,
% 0.22/0.58      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('clc', [status(thm)], ['102', '103'])).
% 0.22/0.58  thf('130', plain,
% 0.22/0.58      (((r2_hidden @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.22/0.58        | (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['128', '129'])).
% 0.22/0.58  thf('131', plain,
% 0.22/0.58      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.58  thf('132', plain,
% 0.22/0.58      (((v1_xboole_0 @ o_0_0_xboole_0)
% 0.22/0.58        | (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C))),
% 0.22/0.58      inference('sup-', [status(thm)], ['130', '131'])).
% 0.22/0.58  thf('133', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.22/0.58      inference('clc', [status(thm)], ['127', '132'])).
% 0.22/0.58  thf('134', plain,
% 0.22/0.58      (![X0 : $i]:
% 0.22/0.58         (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.58  thf('135', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['133', '134'])).
% 0.22/0.58  thf('136', plain,
% 0.22/0.58      ((((o_0_0_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['96', '135'])).
% 0.22/0.58  thf('137', plain,
% 0.22/0.58      ((((sk_C) = (o_0_0_xboole_0))
% 0.22/0.58        | ((o_0_0_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['136'])).
% 0.22/0.58  thf('138', plain, (((sk_C) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.58  thf('139', plain, (((o_0_0_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.22/0.58  thf('140', plain,
% 0.22/0.58      (![X8 : $i, X9 : $i]:
% 0.22/0.58         (((X8) = (o_0_0_xboole_0))
% 0.22/0.58          | ((k1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9)) = (X8))
% 0.22/0.58          | ((X9) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.22/0.58  thf('141', plain,
% 0.22/0.58      ((((k1_relat_1 @ o_0_0_xboole_0) = (sk_A))
% 0.22/0.58        | ((sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('sup+', [status(thm)], ['139', '140'])).
% 0.22/0.58  thf('142', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.22/0.58      inference('sup-', [status(thm)], ['133', '134'])).
% 0.22/0.58  thf('143', plain,
% 0.22/0.58      ((((o_0_0_xboole_0) = (sk_A))
% 0.22/0.58        | ((sk_B) = (o_0_0_xboole_0))
% 0.22/0.58        | ((sk_A) = (o_0_0_xboole_0)))),
% 0.22/0.58      inference('demod', [status(thm)], ['141', '142'])).
% 0.22/0.58  thf('144', plain,
% 0.22/0.58      ((((sk_B) = (o_0_0_xboole_0)) | ((o_0_0_xboole_0) = (sk_A)))),
% 0.22/0.58      inference('simplify', [status(thm)], ['143'])).
% 0.22/0.58  thf('145', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['81', '82'])).
% 0.22/0.58  thf('146', plain, (((sk_B) != (o_0_0_xboole_0))),
% 0.22/0.58      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.58  thf('147', plain, ($false),
% 0.22/0.58      inference('simplify_reflect-', [status(thm)], ['144', '145', '146'])).
% 0.22/0.58  
% 0.22/0.58  % SZS output end Refutation
% 0.22/0.58  
% 0.22/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
