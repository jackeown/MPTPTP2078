%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uKjkKZpnE7

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 146 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  773 (1571 expanded)
%              Number of equality atoms :   71 ( 125 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k3_xboole_0 @ X0 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_A @ sk_C ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_A ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k5_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ sk_B @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X1 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('31',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('37',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('39',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X11 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['24','49'])).

thf('51',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X14 @ X16 @ X15 )
        = ( k9_subset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uKjkKZpnE7
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 175 iterations in 0.119s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(d4_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.38/0.57         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.38/0.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('eq_fact', [status(thm)], ['0'])).
% 0.38/0.57  thf(t32_subset_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ![C:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.38/0.57             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i]:
% 0.38/0.57        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57          ( ![C:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.38/0.57                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.38/0.57  thf('2', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l3_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X19 @ X20)
% 0.38/0.57          | (r2_hidden @ X19 @ X21)
% 0.38/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (((sk_C) = (k3_xboole_0 @ X0 @ sk_C))
% 0.38/0.57          | (r2_hidden @ (sk_D @ sk_C @ sk_C @ X0) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('eq_fact', [status(thm)], ['0'])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.38/0.57         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.38/0.57          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('eq_fact', [status(thm)], ['0'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.38/0.57      inference('clc', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      ((((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))
% 0.38/0.57        | ((sk_C) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '11'])).
% 0.38/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))
% 0.38/0.57        | ((sk_C) = (k3_xboole_0 @ sk_C @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.57  thf('16', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.38/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf(t100_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X9 @ X10)
% 0.38/0.57           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['16', '19'])).
% 0.38/0.57  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d5_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X17 : $i, X18 : $i]:
% 0.38/0.57         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 0.38/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (((k3_subset_1 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['20', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.38/0.57         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.38/0.57          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.57  thf('26', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X19 @ X20)
% 0.38/0.57          | (r2_hidden @ X19 @ X21)
% 0.38/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r2_hidden @ (sk_D @ X1 @ sk_B @ X0) @ X1)
% 0.38/0.57          | ((X1) = (k3_xboole_0 @ X0 @ sk_B))
% 0.38/0.57          | (r2_hidden @ (sk_D @ X1 @ sk_B @ X0) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.38/0.57      inference('clc', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))
% 0.38/0.57        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.57        | ((sk_B) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.38/0.57        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.57        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.57        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.38/0.57        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.38/0.57          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.38/0.57      inference('clc', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.38/0.57        | ((sk_B) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.38/0.57        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf(t112_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.38/0.57       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.57         ((k5_xboole_0 @ (k3_xboole_0 @ X11 @ X13) @ (k3_xboole_0 @ X12 @ X13))
% 0.38/0.57           = (k3_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.38/0.57           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.38/0.57           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.38/0.57      inference('sup+', [status(thm)], ['42', '45'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('48', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_xboole_0 @ sk_B @ X0)
% 0.38/0.57           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.38/0.57         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['24', '49'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      (((k7_subset_1 @ sk_A @ sk_B @ sk_C)
% 0.38/0.57         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('52', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.38/0.57          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.38/0.57         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['51', '54'])).
% 0.38/0.57  thf('56', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(commutativity_k9_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((k9_subset_1 @ X14 @ X16 @ X15) = (k9_subset_1 @ X14 @ X15 @ X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('59', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.57         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.38/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 0.38/0.57      inference('demod', [status(thm)], ['58', '61'])).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((k4_xboole_0 @ sk_B @ sk_C)
% 0.38/0.57         != (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['55', '62', '63'])).
% 0.38/0.57  thf('65', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['50', '64'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
