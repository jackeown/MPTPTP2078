%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zY6lcFnsfR

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:58 EST 2020

% Result     : Theorem 9.16s
% Output     : Refutation 9.16s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 547 expanded)
%              Number of leaves         :   40 ( 192 expanded)
%              Depth                    :   24
%              Number of atoms          : 1169 (4503 expanded)
%              Number of equality atoms :   58 ( 216 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_tarski_type,type,(
    r2_tarski: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k2_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k2_xboole_0 @ X24 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X24 @ X26 ) ) @ X25 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X59 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v1_relat_1 @ X58 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X59 ) @ ( k2_relat_1 @ X58 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X59 @ X58 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['25','29'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('31',plain,(
    ! [X50: $i,X53: $i] :
      ( ( X53
        = ( k2_relat_1 @ X50 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X53 @ X50 ) @ ( sk_C_3 @ X53 @ X50 ) ) @ X50 )
      | ( r2_hidden @ ( sk_C_3 @ X53 @ X50 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('32',plain,(
    ! [X21: $i] :
      ( r1_xboole_0 @ X21 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t136_zfmisc_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ~ ( ( r1_tarski @ C @ B )
            & ~ ( r2_tarski @ C @ B )
            & ~ ( r2_hidden @ C @ B ) )
      & ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) )
      & ! [C: $i,D: $i] :
          ( ( ( r2_hidden @ C @ B )
            & ( r1_tarski @ D @ C ) )
         => ( r2_hidden @ D @ B ) )
      & ( r2_hidden @ A @ B ) ) )).

thf('33',plain,(
    ! [X31: $i] :
      ( r2_hidden @ X31 @ ( sk_B_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t136_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( sk_B_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['30','39','40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k2_relat_1 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['22','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k3_relat_1 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_2 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('59',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X57 ) @ ( k1_relat_1 @ X56 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X57 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf('60',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('61',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('62',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X57 ) @ ( k1_relat_1 @ X56 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X57 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('64',plain,(
    ! [X43: $i,X46: $i] :
      ( ( X46
        = ( k1_relat_1 @ X43 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X46 @ X43 ) @ ( sk_D_1 @ X46 @ X43 ) ) @ X43 )
      | ( r2_hidden @ ( sk_C_2 @ X46 @ X43 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('73',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( k3_tarski @ ( k2_tarski @ X13 @ X12 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X24 @ X26 ) ) @ X25 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ X1 ) ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) )
      | ~ ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','80'])).

thf('82',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('85',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_2 ) @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X8 @ X9 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X55: $i] :
      ( ( ( k3_relat_1 @ X55 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('95',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X24 @ X26 ) ) @ X25 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('101',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('102',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('103',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X25 )
      | ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X24 @ X26 ) ) @ X25 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('107',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_A ) ) )
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('111',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ) )
    = ( k1_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['99','100','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('115',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_B_2 ) ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X1 )
      | ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('117',plain,
    ( ( k3_tarski @ ( k2_tarski @ ( k3_relat_1 @ sk_B_2 ) @ ( k1_relat_1 @ sk_B_2 ) ) )
    = ( k3_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['81','117'])).

thf('119',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zY6lcFnsfR
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.16/9.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.16/9.36  % Solved by: fo/fo7.sh
% 9.16/9.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.16/9.36  % done 13586 iterations in 8.894s
% 9.16/9.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.16/9.36  % SZS output start Refutation
% 9.16/9.36  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 9.16/9.36  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 9.16/9.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.16/9.36  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 9.16/9.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.16/9.36  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 9.16/9.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.16/9.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.16/9.36  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 9.16/9.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.16/9.36  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 9.16/9.36  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.16/9.36  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 9.16/9.36  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 9.16/9.36  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.16/9.36  thf(sk_B_2_type, type, sk_B_2: $i).
% 9.16/9.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.16/9.36  thf(r2_tarski_type, type, r2_tarski: $i > $i > $o).
% 9.16/9.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.16/9.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.16/9.36  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 9.16/9.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.16/9.36  thf(sk_A_type, type, sk_A: $i).
% 9.16/9.36  thf(t31_relat_1, conjecture,
% 9.16/9.36    (![A:$i]:
% 9.16/9.36     ( ( v1_relat_1 @ A ) =>
% 9.16/9.36       ( ![B:$i]:
% 9.16/9.36         ( ( v1_relat_1 @ B ) =>
% 9.16/9.36           ( ( r1_tarski @ A @ B ) =>
% 9.16/9.36             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 9.16/9.36  thf(zf_stmt_0, negated_conjecture,
% 9.16/9.36    (~( ![A:$i]:
% 9.16/9.36        ( ( v1_relat_1 @ A ) =>
% 9.16/9.36          ( ![B:$i]:
% 9.16/9.36            ( ( v1_relat_1 @ B ) =>
% 9.16/9.36              ( ( r1_tarski @ A @ B ) =>
% 9.16/9.36                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 9.16/9.36    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 9.16/9.36  thf('0', plain,
% 9.16/9.36      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf(d6_relat_1, axiom,
% 9.16/9.36    (![A:$i]:
% 9.16/9.36     ( ( v1_relat_1 @ A ) =>
% 9.16/9.36       ( ( k3_relat_1 @ A ) =
% 9.16/9.36         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 9.16/9.36  thf('1', plain,
% 9.16/9.36      (![X55 : $i]:
% 9.16/9.36         (((k3_relat_1 @ X55)
% 9.16/9.36            = (k2_xboole_0 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55)))
% 9.16/9.36          | ~ (v1_relat_1 @ X55))),
% 9.16/9.36      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.16/9.36  thf(l51_zfmisc_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.16/9.36  thf('2', plain,
% 9.16/9.36      (![X29 : $i, X30 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 9.16/9.36      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.16/9.36  thf('3', plain,
% 9.16/9.36      (![X55 : $i]:
% 9.16/9.36         (((k3_relat_1 @ X55)
% 9.16/9.36            = (k3_tarski @ 
% 9.16/9.36               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 9.16/9.36          | ~ (v1_relat_1 @ X55))),
% 9.16/9.36      inference('demod', [status(thm)], ['1', '2'])).
% 9.16/9.36  thf(t7_xboole_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.16/9.36  thf('4', plain,
% 9.16/9.36      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 9.16/9.36      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.16/9.36  thf('5', plain,
% 9.16/9.36      (![X29 : $i, X30 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 9.16/9.36      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.16/9.36  thf('6', plain,
% 9.16/9.36      (![X22 : $i, X23 : $i]:
% 9.16/9.36         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 9.16/9.36      inference('demod', [status(thm)], ['4', '5'])).
% 9.16/9.36  thf(d10_xboole_0, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.16/9.36  thf('7', plain,
% 9.16/9.36      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 9.16/9.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.16/9.36  thf('8', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.16/9.36      inference('simplify', [status(thm)], ['7'])).
% 9.16/9.36  thf(t10_xboole_1, axiom,
% 9.16/9.36    (![A:$i,B:$i,C:$i]:
% 9.16/9.36     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 9.16/9.36  thf('9', plain,
% 9.16/9.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X11 @ X12)
% 9.16/9.36          | (r1_tarski @ X11 @ (k2_xboole_0 @ X13 @ X12)))),
% 9.16/9.36      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.16/9.36  thf('10', plain,
% 9.16/9.36      (![X29 : $i, X30 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 9.16/9.36      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.16/9.36  thf('11', plain,
% 9.16/9.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X11 @ X12)
% 9.16/9.36          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 9.16/9.36      inference('demod', [status(thm)], ['9', '10'])).
% 9.16/9.36  thf('12', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['8', '11'])).
% 9.16/9.36  thf(t8_xboole_1, axiom,
% 9.16/9.36    (![A:$i,B:$i,C:$i]:
% 9.16/9.36     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 9.16/9.36       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 9.16/9.36  thf('13', plain,
% 9.16/9.36      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X24 @ X25)
% 9.16/9.36          | ~ (r1_tarski @ X26 @ X25)
% 9.16/9.36          | (r1_tarski @ (k2_xboole_0 @ X24 @ X26) @ X25))),
% 9.16/9.36      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.16/9.36  thf('14', plain,
% 9.16/9.36      (![X29 : $i, X30 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 9.16/9.36      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.16/9.36  thf('15', plain,
% 9.16/9.36      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X24 @ X25)
% 9.16/9.36          | ~ (r1_tarski @ X26 @ X25)
% 9.16/9.36          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X24 @ X26)) @ X25))),
% 9.16/9.36      inference('demod', [status(thm)], ['13', '14'])).
% 9.16/9.36  thf('16', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.16/9.36         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X2)) @ 
% 9.16/9.36           (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 9.16/9.36          | ~ (r1_tarski @ X2 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['12', '15'])).
% 9.16/9.36  thf('17', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['6', '16'])).
% 9.16/9.36  thf('18', plain,
% 9.16/9.36      (![X5 : $i, X7 : $i]:
% 9.16/9.36         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 9.16/9.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.16/9.36  thf('19', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ 
% 9.16/9.36             (k3_tarski @ (k2_tarski @ X0 @ X1)))
% 9.16/9.36          | ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 9.16/9.36              = (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['17', '18'])).
% 9.16/9.36  thf('20', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['6', '16'])).
% 9.16/9.36  thf('21', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 9.16/9.36           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 9.16/9.36      inference('demod', [status(thm)], ['19', '20'])).
% 9.16/9.36  thf('22', plain,
% 9.16/9.36      (![X55 : $i]:
% 9.16/9.36         (((k3_relat_1 @ X55)
% 9.16/9.36            = (k3_tarski @ 
% 9.16/9.36               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 9.16/9.36          | ~ (v1_relat_1 @ X55))),
% 9.16/9.36      inference('demod', [status(thm)], ['1', '2'])).
% 9.16/9.36  thf('23', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf(l32_xboole_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.16/9.36  thf('24', plain,
% 9.16/9.36      (![X8 : $i, X10 : $i]:
% 9.16/9.36         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 9.16/9.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.16/9.36  thf('25', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['23', '24'])).
% 9.16/9.36  thf(t28_relat_1, axiom,
% 9.16/9.36    (![A:$i]:
% 9.16/9.36     ( ( v1_relat_1 @ A ) =>
% 9.16/9.36       ( ![B:$i]:
% 9.16/9.36         ( ( v1_relat_1 @ B ) =>
% 9.16/9.36           ( r1_tarski @
% 9.16/9.36             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 9.16/9.36             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 9.16/9.36  thf('26', plain,
% 9.16/9.36      (![X58 : $i, X59 : $i]:
% 9.16/9.36         (~ (v1_relat_1 @ X58)
% 9.16/9.36          | (r1_tarski @ 
% 9.16/9.36             (k6_subset_1 @ (k2_relat_1 @ X59) @ (k2_relat_1 @ X58)) @ 
% 9.16/9.36             (k2_relat_1 @ (k6_subset_1 @ X59 @ X58)))
% 9.16/9.36          | ~ (v1_relat_1 @ X59))),
% 9.16/9.36      inference('cnf', [status(esa)], [t28_relat_1])).
% 9.16/9.36  thf(redefinition_k6_subset_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.16/9.36  thf('27', plain,
% 9.16/9.36      (![X39 : $i, X40 : $i]:
% 9.16/9.36         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 9.16/9.36      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.16/9.36  thf('28', plain,
% 9.16/9.36      (![X39 : $i, X40 : $i]:
% 9.16/9.36         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 9.16/9.36      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.16/9.36  thf('29', plain,
% 9.16/9.36      (![X58 : $i, X59 : $i]:
% 9.16/9.36         (~ (v1_relat_1 @ X58)
% 9.16/9.36          | (r1_tarski @ 
% 9.16/9.36             (k4_xboole_0 @ (k2_relat_1 @ X59) @ (k2_relat_1 @ X58)) @ 
% 9.16/9.36             (k2_relat_1 @ (k4_xboole_0 @ X59 @ X58)))
% 9.16/9.36          | ~ (v1_relat_1 @ X59))),
% 9.16/9.36      inference('demod', [status(thm)], ['26', '27', '28'])).
% 9.16/9.36  thf('30', plain,
% 9.16/9.36      (((r1_tarski @ 
% 9.16/9.36         (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 9.16/9.36         (k2_relat_1 @ k1_xboole_0))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_A)
% 9.16/9.36        | ~ (v1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup+', [status(thm)], ['25', '29'])).
% 9.16/9.36  thf(d5_relat_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 9.16/9.36       ( ![C:$i]:
% 9.16/9.36         ( ( r2_hidden @ C @ B ) <=>
% 9.16/9.36           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 9.16/9.36  thf('31', plain,
% 9.16/9.36      (![X50 : $i, X53 : $i]:
% 9.16/9.36         (((X53) = (k2_relat_1 @ X50))
% 9.16/9.36          | (r2_hidden @ 
% 9.16/9.36             (k4_tarski @ (sk_D_3 @ X53 @ X50) @ (sk_C_3 @ X53 @ X50)) @ X50)
% 9.16/9.36          | (r2_hidden @ (sk_C_3 @ X53 @ X50) @ X53))),
% 9.16/9.36      inference('cnf', [status(esa)], [d5_relat_1])).
% 9.16/9.36  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 9.16/9.36  thf('32', plain, (![X21 : $i]: (r1_xboole_0 @ X21 @ k1_xboole_0)),
% 9.16/9.36      inference('cnf', [status(esa)], [t65_xboole_1])).
% 9.16/9.36  thf(t136_zfmisc_1, axiom,
% 9.16/9.36    (![A:$i]:
% 9.16/9.36     ( ?[B:$i]:
% 9.16/9.36       ( ( ![C:$i]:
% 9.16/9.36           ( ~( ( r1_tarski @ C @ B ) & ( ~( r2_tarski @ C @ B ) ) & 
% 9.16/9.36                ( ~( r2_hidden @ C @ B ) ) ) ) ) & 
% 9.16/9.36         ( ![C:$i]:
% 9.16/9.36           ( ( r2_hidden @ C @ B ) => ( r2_hidden @ ( k1_zfmisc_1 @ C ) @ B ) ) ) & 
% 9.16/9.36         ( ![C:$i,D:$i]:
% 9.16/9.36           ( ( ( r2_hidden @ C @ B ) & ( r1_tarski @ D @ C ) ) =>
% 9.16/9.36             ( r2_hidden @ D @ B ) ) ) & 
% 9.16/9.36         ( r2_hidden @ A @ B ) ) ))).
% 9.16/9.36  thf('33', plain, (![X31 : $i]: (r2_hidden @ X31 @ (sk_B_1 @ X31))),
% 9.16/9.36      inference('cnf', [status(esa)], [t136_zfmisc_1])).
% 9.16/9.36  thf(t3_xboole_0, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 9.16/9.36            ( r1_xboole_0 @ A @ B ) ) ) & 
% 9.16/9.36       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 9.16/9.36            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 9.16/9.36  thf('34', plain,
% 9.16/9.36      (![X0 : $i, X2 : $i, X3 : $i]:
% 9.16/9.36         (~ (r2_hidden @ X2 @ X0)
% 9.16/9.36          | ~ (r2_hidden @ X2 @ X3)
% 9.16/9.36          | ~ (r1_xboole_0 @ X0 @ X3))),
% 9.16/9.36      inference('cnf', [status(esa)], [t3_xboole_0])).
% 9.16/9.36  thf('35', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (~ (r1_xboole_0 @ (sk_B_1 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 9.16/9.36      inference('sup-', [status(thm)], ['33', '34'])).
% 9.16/9.36  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 9.16/9.36      inference('sup-', [status(thm)], ['32', '35'])).
% 9.16/9.36  thf('37', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 9.16/9.36          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['31', '36'])).
% 9.16/9.36  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 9.16/9.36      inference('sup-', [status(thm)], ['32', '35'])).
% 9.16/9.36  thf('39', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['37', '38'])).
% 9.16/9.36  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('41', plain, ((v1_relat_1 @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('42', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)) @ 
% 9.16/9.36        k1_xboole_0)),
% 9.16/9.36      inference('demod', [status(thm)], ['30', '39', '40', '41'])).
% 9.16/9.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.16/9.36  thf('43', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 9.16/9.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.16/9.36  thf('44', plain,
% 9.16/9.36      (![X5 : $i, X7 : $i]:
% 9.16/9.36         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 9.16/9.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.16/9.36  thf('45', plain,
% 9.16/9.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['43', '44'])).
% 9.16/9.36  thf('46', plain,
% 9.16/9.36      (((k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))
% 9.16/9.36         = (k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['42', '45'])).
% 9.16/9.36  thf('47', plain,
% 9.16/9.36      (![X8 : $i, X9 : $i]:
% 9.16/9.36         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 9.16/9.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.16/9.36  thf('48', plain,
% 9.16/9.36      ((((k1_xboole_0) != (k1_xboole_0))
% 9.16/9.36        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['46', '47'])).
% 9.16/9.36  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('simplify', [status(thm)], ['48'])).
% 9.16/9.36  thf('50', plain,
% 9.16/9.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X11 @ X12)
% 9.16/9.36          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 9.16/9.36      inference('demod', [status(thm)], ['9', '10'])).
% 9.16/9.36  thf('51', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X0 @ (k2_relat_1 @ sk_B_2))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['49', '50'])).
% 9.16/9.36  thf('52', plain,
% 9.16/9.36      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup+', [status(thm)], ['22', '51'])).
% 9.16/9.36  thf('53', plain, ((v1_relat_1 @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('54', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('demod', [status(thm)], ['52', '53'])).
% 9.16/9.36  thf('55', plain,
% 9.16/9.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X11 @ X12)
% 9.16/9.36          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 9.16/9.36      inference('demod', [status(thm)], ['9', '10'])).
% 9.16/9.36  thf('56', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X0 @ (k3_relat_1 @ sk_B_2))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['54', '55'])).
% 9.16/9.36  thf('57', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ (k3_relat_1 @ sk_B_2) @ X0)))),
% 9.16/9.36      inference('sup+', [status(thm)], ['21', '56'])).
% 9.16/9.36  thf('58', plain, (((k4_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['23', '24'])).
% 9.16/9.36  thf(t15_relat_1, axiom,
% 9.16/9.36    (![A:$i]:
% 9.16/9.36     ( ( v1_relat_1 @ A ) =>
% 9.16/9.36       ( ![B:$i]:
% 9.16/9.36         ( ( v1_relat_1 @ B ) =>
% 9.16/9.36           ( r1_tarski @
% 9.16/9.36             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 9.16/9.36             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 9.16/9.36  thf('59', plain,
% 9.16/9.36      (![X56 : $i, X57 : $i]:
% 9.16/9.36         (~ (v1_relat_1 @ X56)
% 9.16/9.36          | (r1_tarski @ 
% 9.16/9.36             (k6_subset_1 @ (k1_relat_1 @ X57) @ (k1_relat_1 @ X56)) @ 
% 9.16/9.36             (k1_relat_1 @ (k6_subset_1 @ X57 @ X56)))
% 9.16/9.36          | ~ (v1_relat_1 @ X57))),
% 9.16/9.36      inference('cnf', [status(esa)], [t15_relat_1])).
% 9.16/9.36  thf('60', plain,
% 9.16/9.36      (![X39 : $i, X40 : $i]:
% 9.16/9.36         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 9.16/9.36      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.16/9.36  thf('61', plain,
% 9.16/9.36      (![X39 : $i, X40 : $i]:
% 9.16/9.36         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 9.16/9.36      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.16/9.36  thf('62', plain,
% 9.16/9.36      (![X56 : $i, X57 : $i]:
% 9.16/9.36         (~ (v1_relat_1 @ X56)
% 9.16/9.36          | (r1_tarski @ 
% 9.16/9.36             (k4_xboole_0 @ (k1_relat_1 @ X57) @ (k1_relat_1 @ X56)) @ 
% 9.16/9.36             (k1_relat_1 @ (k4_xboole_0 @ X57 @ X56)))
% 9.16/9.36          | ~ (v1_relat_1 @ X57))),
% 9.16/9.36      inference('demod', [status(thm)], ['59', '60', '61'])).
% 9.16/9.36  thf('63', plain,
% 9.16/9.36      (((r1_tarski @ 
% 9.16/9.36         (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)) @ 
% 9.16/9.36         (k1_relat_1 @ k1_xboole_0))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_A)
% 9.16/9.36        | ~ (v1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup+', [status(thm)], ['58', '62'])).
% 9.16/9.36  thf(d4_relat_1, axiom,
% 9.16/9.36    (![A:$i,B:$i]:
% 9.16/9.36     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 9.16/9.36       ( ![C:$i]:
% 9.16/9.36         ( ( r2_hidden @ C @ B ) <=>
% 9.16/9.36           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 9.16/9.36  thf('64', plain,
% 9.16/9.36      (![X43 : $i, X46 : $i]:
% 9.16/9.36         (((X46) = (k1_relat_1 @ X43))
% 9.16/9.36          | (r2_hidden @ 
% 9.16/9.36             (k4_tarski @ (sk_C_2 @ X46 @ X43) @ (sk_D_1 @ X46 @ X43)) @ X43)
% 9.16/9.36          | (r2_hidden @ (sk_C_2 @ X46 @ X43) @ X46))),
% 9.16/9.36      inference('cnf', [status(esa)], [d4_relat_1])).
% 9.16/9.36  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 9.16/9.36      inference('sup-', [status(thm)], ['32', '35'])).
% 9.16/9.36  thf('66', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         ((r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0)
% 9.16/9.36          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['64', '65'])).
% 9.16/9.36  thf('67', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 9.16/9.36      inference('sup-', [status(thm)], ['32', '35'])).
% 9.16/9.36  thf('68', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['66', '67'])).
% 9.16/9.36  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('70', plain, ((v1_relat_1 @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('71', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)) @ 
% 9.16/9.36        k1_xboole_0)),
% 9.16/9.36      inference('demod', [status(thm)], ['63', '68', '69', '70'])).
% 9.16/9.36  thf('72', plain,
% 9.16/9.36      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['43', '44'])).
% 9.16/9.36  thf('73', plain,
% 9.16/9.36      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))
% 9.16/9.36         = (k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['71', '72'])).
% 9.16/9.36  thf('74', plain,
% 9.16/9.36      (![X8 : $i, X9 : $i]:
% 9.16/9.36         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 9.16/9.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.16/9.36  thf('75', plain,
% 9.16/9.36      ((((k1_xboole_0) != (k1_xboole_0))
% 9.16/9.36        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['73', '74'])).
% 9.16/9.36  thf('76', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('simplify', [status(thm)], ['75'])).
% 9.16/9.36  thf('77', plain,
% 9.16/9.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X11 @ X12)
% 9.16/9.36          | (r1_tarski @ X11 @ (k3_tarski @ (k2_tarski @ X13 @ X12))))),
% 9.16/9.36      inference('demod', [status(thm)], ['9', '10'])).
% 9.16/9.36  thf('78', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_2))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['76', '77'])).
% 9.16/9.36  thf('79', plain,
% 9.16/9.36      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X24 @ X25)
% 9.16/9.36          | ~ (r1_tarski @ X26 @ X25)
% 9.16/9.36          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X24 @ X26)) @ X25))),
% 9.16/9.36      inference('demod', [status(thm)], ['13', '14'])).
% 9.16/9.36  thf('80', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ X1)) @ 
% 9.16/9.36           (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_2))))
% 9.16/9.36          | ~ (r1_tarski @ X1 @ 
% 9.16/9.36               (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_2)))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['78', '79'])).
% 9.16/9.36  thf('81', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) @ 
% 9.16/9.36        (k3_tarski @ 
% 9.16/9.36         (k2_tarski @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_B_2))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['57', '80'])).
% 9.16/9.36  thf('82', plain,
% 9.16/9.36      (![X55 : $i]:
% 9.16/9.36         (((k3_relat_1 @ X55)
% 9.16/9.36            = (k3_tarski @ 
% 9.16/9.36               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 9.16/9.36          | ~ (v1_relat_1 @ X55))),
% 9.16/9.36      inference('demod', [status(thm)], ['1', '2'])).
% 9.16/9.36  thf('83', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 9.16/9.36           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 9.16/9.36      inference('demod', [status(thm)], ['19', '20'])).
% 9.16/9.36  thf('84', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 9.16/9.36          (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_2))))),
% 9.16/9.36      inference('sup-', [status(thm)], ['76', '77'])).
% 9.16/9.36  thf('85', plain,
% 9.16/9.36      (![X8 : $i, X10 : $i]:
% 9.16/9.36         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 9.16/9.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.16/9.36  thf('86', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         ((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 9.16/9.36           (k3_tarski @ (k2_tarski @ X0 @ (k1_relat_1 @ sk_B_2))))
% 9.16/9.36           = (k1_xboole_0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['84', '85'])).
% 9.16/9.36  thf('87', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         ((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 9.16/9.36           (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_2) @ X0)))
% 9.16/9.36           = (k1_xboole_0))),
% 9.16/9.36      inference('sup+', [status(thm)], ['83', '86'])).
% 9.16/9.36  thf('88', plain,
% 9.16/9.36      ((((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))
% 9.16/9.36          = (k1_xboole_0))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup+', [status(thm)], ['82', '87'])).
% 9.16/9.36  thf('89', plain, ((v1_relat_1 @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('90', plain,
% 9.16/9.36      (((k4_xboole_0 @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))
% 9.16/9.36         = (k1_xboole_0))),
% 9.16/9.36      inference('demod', [status(thm)], ['88', '89'])).
% 9.16/9.36  thf('91', plain,
% 9.16/9.36      (![X8 : $i, X9 : $i]:
% 9.16/9.36         ((r1_tarski @ X8 @ X9) | ((k4_xboole_0 @ X8 @ X9) != (k1_xboole_0)))),
% 9.16/9.36      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.16/9.36  thf('92', plain,
% 9.16/9.36      ((((k1_xboole_0) != (k1_xboole_0))
% 9.16/9.36        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['90', '91'])).
% 9.16/9.36  thf('93', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('simplify', [status(thm)], ['92'])).
% 9.16/9.36  thf('94', plain,
% 9.16/9.36      (![X55 : $i]:
% 9.16/9.36         (((k3_relat_1 @ X55)
% 9.16/9.36            = (k3_tarski @ 
% 9.16/9.36               (k2_tarski @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 9.16/9.36          | ~ (v1_relat_1 @ X55))),
% 9.16/9.36      inference('demod', [status(thm)], ['1', '2'])).
% 9.16/9.36  thf('95', plain,
% 9.16/9.36      (![X22 : $i, X23 : $i]:
% 9.16/9.36         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 9.16/9.36      inference('demod', [status(thm)], ['4', '5'])).
% 9.16/9.36  thf('96', plain,
% 9.16/9.36      (![X0 : $i]:
% 9.16/9.36         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 9.16/9.36          | ~ (v1_relat_1 @ X0))),
% 9.16/9.36      inference('sup+', [status(thm)], ['94', '95'])).
% 9.16/9.36  thf('97', plain,
% 9.16/9.36      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X24 @ X25)
% 9.16/9.36          | ~ (r1_tarski @ X26 @ X25)
% 9.16/9.36          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X24 @ X26)) @ X25))),
% 9.16/9.36      inference('demod', [status(thm)], ['13', '14'])).
% 9.16/9.36  thf('98', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (~ (v1_relat_1 @ X0)
% 9.16/9.36          | (r1_tarski @ (k3_tarski @ (k2_tarski @ (k1_relat_1 @ X0) @ X1)) @ 
% 9.16/9.36             (k3_relat_1 @ X0))
% 9.16/9.36          | ~ (r1_tarski @ X1 @ (k3_relat_1 @ X0)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['96', '97'])).
% 9.16/9.36  thf('99', plain,
% 9.16/9.36      (((r1_tarski @ 
% 9.16/9.36         (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A))) @ 
% 9.16/9.36         (k3_relat_1 @ sk_B_2))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup-', [status(thm)], ['93', '98'])).
% 9.16/9.36  thf('100', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 9.16/9.36           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 9.16/9.36      inference('demod', [status(thm)], ['19', '20'])).
% 9.16/9.36  thf('101', plain,
% 9.16/9.36      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('simplify', [status(thm)], ['75'])).
% 9.16/9.36  thf('102', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 9.16/9.36      inference('simplify', [status(thm)], ['7'])).
% 9.16/9.36  thf('103', plain,
% 9.16/9.36      (![X24 : $i, X25 : $i, X26 : $i]:
% 9.16/9.36         (~ (r1_tarski @ X24 @ X25)
% 9.16/9.36          | ~ (r1_tarski @ X26 @ X25)
% 9.16/9.36          | (r1_tarski @ (k3_tarski @ (k2_tarski @ X24 @ X26)) @ X25))),
% 9.16/9.36      inference('demod', [status(thm)], ['13', '14'])).
% 9.16/9.36  thf('104', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 9.16/9.36          | ~ (r1_tarski @ X1 @ X0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['102', '103'])).
% 9.16/9.36  thf('105', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A))) @ 
% 9.16/9.36        (k1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup-', [status(thm)], ['101', '104'])).
% 9.16/9.36  thf('106', plain,
% 9.16/9.36      (![X22 : $i, X23 : $i]:
% 9.16/9.36         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 9.16/9.36      inference('demod', [status(thm)], ['4', '5'])).
% 9.16/9.36  thf('107', plain,
% 9.16/9.36      (![X5 : $i, X7 : $i]:
% 9.16/9.36         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 9.16/9.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.16/9.36  thf('108', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 9.16/9.36          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['106', '107'])).
% 9.16/9.36  thf('109', plain,
% 9.16/9.36      (((k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_A)))
% 9.16/9.36         = (k1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup-', [status(thm)], ['105', '108'])).
% 9.16/9.36  thf('110', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((k3_tarski @ (k2_tarski @ X1 @ X0))
% 9.16/9.36           = (k3_tarski @ (k2_tarski @ X0 @ X1)))),
% 9.16/9.36      inference('demod', [status(thm)], ['19', '20'])).
% 9.16/9.36  thf('111', plain,
% 9.16/9.36      (((k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B_2)))
% 9.16/9.36         = (k1_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('demod', [status(thm)], ['109', '110'])).
% 9.16/9.36  thf('112', plain, ((v1_relat_1 @ sk_B_2)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('113', plain,
% 9.16/9.36      ((r1_tarski @ (k1_relat_1 @ sk_B_2) @ (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('demod', [status(thm)], ['99', '100', '111', '112'])).
% 9.16/9.36  thf('114', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         ((r1_tarski @ (k3_tarski @ (k2_tarski @ X0 @ X1)) @ X0)
% 9.16/9.36          | ~ (r1_tarski @ X1 @ X0))),
% 9.16/9.36      inference('sup-', [status(thm)], ['102', '103'])).
% 9.16/9.36  thf('115', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k3_tarski @ 
% 9.16/9.36         (k2_tarski @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_B_2))) @ 
% 9.16/9.36        (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup-', [status(thm)], ['113', '114'])).
% 9.16/9.36  thf('116', plain,
% 9.16/9.36      (![X0 : $i, X1 : $i]:
% 9.16/9.36         (~ (r1_tarski @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X1)
% 9.16/9.36          | ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 9.16/9.36      inference('sup-', [status(thm)], ['106', '107'])).
% 9.16/9.36  thf('117', plain,
% 9.16/9.36      (((k3_tarski @ 
% 9.16/9.36         (k2_tarski @ (k3_relat_1 @ sk_B_2) @ (k1_relat_1 @ sk_B_2)))
% 9.16/9.36         = (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('sup-', [status(thm)], ['115', '116'])).
% 9.16/9.36  thf('118', plain,
% 9.16/9.36      ((r1_tarski @ 
% 9.16/9.36        (k3_tarski @ (k2_tarski @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) @ 
% 9.16/9.36        (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('demod', [status(thm)], ['81', '117'])).
% 9.16/9.36  thf('119', plain,
% 9.16/9.36      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))
% 9.16/9.36        | ~ (v1_relat_1 @ sk_A))),
% 9.16/9.36      inference('sup+', [status(thm)], ['3', '118'])).
% 9.16/9.36  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 9.16/9.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.16/9.36  thf('121', plain,
% 9.16/9.36      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_2))),
% 9.16/9.36      inference('demod', [status(thm)], ['119', '120'])).
% 9.16/9.36  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 9.16/9.36  
% 9.16/9.36  % SZS output end Refutation
% 9.16/9.36  
% 9.16/9.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
