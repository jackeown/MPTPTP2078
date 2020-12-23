%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gCe3iqpp37

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 9.46s
% Output     : Refutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 133 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  759 (1293 expanded)
%              Number of equality atoms :   52 (  80 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t33_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
              = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference(simplify,[status(thm)],['27'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_A @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('52',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['51','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','64','65'])).

thf('67',plain,(
    ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['13','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gCe3iqpp37
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:27:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 9.46/9.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.46/9.66  % Solved by: fo/fo7.sh
% 9.46/9.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.46/9.66  % done 4242 iterations in 9.194s
% 9.46/9.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.46/9.66  % SZS output start Refutation
% 9.46/9.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.46/9.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.46/9.66  thf(sk_B_type, type, sk_B: $i).
% 9.46/9.66  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.46/9.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 9.46/9.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 9.46/9.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.46/9.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.46/9.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.46/9.66  thf(sk_A_type, type, sk_A: $i).
% 9.46/9.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.46/9.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.46/9.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.46/9.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.46/9.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.46/9.66  thf(t33_subset_1, conjecture,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( ![C:$i]:
% 9.46/9.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 9.46/9.66             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 9.46/9.66  thf(zf_stmt_0, negated_conjecture,
% 9.46/9.66    (~( ![A:$i,B:$i]:
% 9.46/9.66        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66          ( ![C:$i]:
% 9.46/9.66            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66              ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 9.46/9.66                ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ) )),
% 9.46/9.66    inference('cnf.neg', [status(esa)], [t33_subset_1])).
% 9.46/9.66  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(dt_k3_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.46/9.66  thf('2', plain,
% 9.46/9.66      (![X20 : $i, X21 : $i]:
% 9.46/9.66         ((m1_subset_1 @ (k3_subset_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))
% 9.46/9.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 9.46/9.66      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.46/9.66  thf('3', plain,
% 9.46/9.66      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['1', '2'])).
% 9.46/9.66  thf(redefinition_k4_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.46/9.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.46/9.66       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.46/9.66  thf('4', plain,
% 9.46/9.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.46/9.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 9.46/9.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 9.46/9.66          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 9.46/9.66      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.46/9.66  thf('5', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 9.46/9.66            = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 9.46/9.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 9.46/9.66      inference('sup-', [status(thm)], ['3', '4'])).
% 9.46/9.66  thf('6', plain,
% 9.46/9.66      (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)
% 9.46/9.66         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 9.46/9.66      inference('sup-', [status(thm)], ['0', '5'])).
% 9.46/9.66  thf(commutativity_k2_xboole_0, axiom,
% 9.46/9.66    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.46/9.66  thf('7', plain,
% 9.46/9.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.46/9.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.46/9.66  thf('8', plain,
% 9.46/9.66      (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)
% 9.46/9.66         = (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.46/9.66      inference('demod', [status(thm)], ['6', '7'])).
% 9.46/9.66  thf('9', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ (k7_subset_1 @ sk_A @ sk_B @ sk_C_1))
% 9.46/9.66         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(redefinition_k7_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.46/9.66  thf('11', plain,
% 9.46/9.66      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.46/9.66         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 9.46/9.66          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 9.46/9.66      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.46/9.66  thf('12', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 9.46/9.66      inference('sup-', [status(thm)], ['10', '11'])).
% 9.46/9.66  thf('13', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 9.46/9.66         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 9.46/9.66      inference('demod', [status(thm)], ['9', '12'])).
% 9.46/9.66  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(d5_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.46/9.66  thf('15', plain,
% 9.46/9.66      (![X18 : $i, X19 : $i]:
% 9.46/9.66         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 9.46/9.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 9.46/9.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.46/9.66  thf('16', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 9.46/9.66      inference('sup-', [status(thm)], ['14', '15'])).
% 9.46/9.66  thf(t48_xboole_1, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.46/9.66  thf('17', plain,
% 9.46/9.66      (![X10 : $i, X11 : $i]:
% 9.46/9.66         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 9.46/9.66           = (k3_xboole_0 @ X10 @ X11))),
% 9.46/9.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.46/9.66  thf('18', plain,
% 9.46/9.66      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 9.46/9.66         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 9.46/9.66      inference('sup+', [status(thm)], ['16', '17'])).
% 9.46/9.66  thf(commutativity_k3_xboole_0, axiom,
% 9.46/9.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.46/9.66  thf('19', plain,
% 9.46/9.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.46/9.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.46/9.66  thf('20', plain,
% 9.46/9.66      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 9.46/9.66         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 9.46/9.66      inference('demod', [status(thm)], ['18', '19'])).
% 9.46/9.66  thf(d3_tarski, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( r1_tarski @ A @ B ) <=>
% 9.46/9.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.46/9.66  thf('21', plain,
% 9.46/9.66      (![X5 : $i, X7 : $i]:
% 9.46/9.66         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 9.46/9.66      inference('cnf', [status(esa)], [d3_tarski])).
% 9.46/9.66  thf('22', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(l3_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 9.46/9.66  thf('23', plain,
% 9.46/9.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.46/9.66         (~ (r2_hidden @ X25 @ X26)
% 9.46/9.66          | (r2_hidden @ X25 @ X27)
% 9.46/9.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 9.46/9.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 9.46/9.66  thf('24', plain,
% 9.46/9.66      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 9.46/9.66      inference('sup-', [status(thm)], ['22', '23'])).
% 9.46/9.66  thf('25', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((r1_tarski @ sk_C_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['21', '24'])).
% 9.46/9.66  thf('26', plain,
% 9.46/9.66      (![X5 : $i, X7 : $i]:
% 9.46/9.66         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 9.46/9.66      inference('cnf', [status(esa)], [d3_tarski])).
% 9.46/9.66  thf('27', plain,
% 9.46/9.66      (((r1_tarski @ sk_C_1 @ sk_A) | (r1_tarski @ sk_C_1 @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['25', '26'])).
% 9.46/9.66  thf('28', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 9.46/9.66      inference('simplify', [status(thm)], ['27'])).
% 9.46/9.66  thf(t28_xboole_1, axiom,
% 9.46/9.66    (![A:$i,B:$i]:
% 9.46/9.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.46/9.66  thf('29', plain,
% 9.46/9.66      (![X8 : $i, X9 : $i]:
% 9.46/9.66         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 9.46/9.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.46/9.66  thf('30', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 9.46/9.66      inference('sup-', [status(thm)], ['28', '29'])).
% 9.46/9.66  thf('31', plain,
% 9.46/9.66      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 9.46/9.66      inference('demod', [status(thm)], ['20', '30'])).
% 9.46/9.66  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf('33', plain,
% 9.46/9.66      (![X18 : $i, X19 : $i]:
% 9.46/9.66         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 9.46/9.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 9.46/9.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.46/9.66  thf('34', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 9.46/9.66      inference('sup-', [status(thm)], ['32', '33'])).
% 9.46/9.66  thf(t54_xboole_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 9.46/9.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 9.46/9.66  thf('35', plain,
% 9.46/9.66      (![X15 : $i, X16 : $i, X17 : $i]:
% 9.46/9.66         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X16 @ X17))
% 9.46/9.66           = (k2_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ 
% 9.46/9.66              (k4_xboole_0 @ X15 @ X17)))),
% 9.46/9.66      inference('cnf', [status(esa)], [t54_xboole_1])).
% 9.46/9.66  thf('36', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 9.46/9.66           = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 9.46/9.66              (k4_xboole_0 @ sk_A @ X0)))),
% 9.46/9.66      inference('sup+', [status(thm)], ['34', '35'])).
% 9.46/9.66  thf('37', plain,
% 9.46/9.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.46/9.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.46/9.66  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(dt_k9_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.46/9.66  thf('39', plain,
% 9.46/9.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.46/9.66         ((m1_subset_1 @ (k9_subset_1 @ X22 @ X23 @ X24) @ (k1_zfmisc_1 @ X22))
% 9.46/9.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X22)))),
% 9.46/9.66      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 9.46/9.66  thf('40', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         (m1_subset_1 @ (k9_subset_1 @ sk_A @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['38', '39'])).
% 9.46/9.66  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf(redefinition_k9_subset_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.46/9.66       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 9.46/9.66  thf('42', plain,
% 9.46/9.66      (![X34 : $i, X35 : $i, X36 : $i]:
% 9.46/9.66         (((k9_subset_1 @ X36 @ X34 @ X35) = (k3_xboole_0 @ X34 @ X35))
% 9.46/9.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 9.46/9.66      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 9.46/9.66  thf('43', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 9.46/9.66      inference('sup-', [status(thm)], ['41', '42'])).
% 9.46/9.66  thf('44', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('demod', [status(thm)], ['40', '43'])).
% 9.46/9.66  thf('45', plain,
% 9.46/9.66      (![X18 : $i, X19 : $i]:
% 9.46/9.66         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 9.46/9.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 9.46/9.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.46/9.66  thf('46', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 9.46/9.66           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 9.46/9.66      inference('sup-', [status(thm)], ['44', '45'])).
% 9.46/9.66  thf('47', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 9.46/9.66           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 9.46/9.66      inference('sup+', [status(thm)], ['37', '46'])).
% 9.46/9.66  thf('48', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k3_subset_1 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 9.46/9.66           = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 9.46/9.66              (k4_xboole_0 @ sk_A @ X0)))),
% 9.46/9.66      inference('demod', [status(thm)], ['36', '47'])).
% 9.46/9.66  thf('49', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ 
% 9.46/9.66         (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 9.46/9.66         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 9.46/9.66      inference('sup+', [status(thm)], ['31', '48'])).
% 9.46/9.66  thf('50', plain,
% 9.46/9.66      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.46/9.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.46/9.66  thf('51', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 9.46/9.66      inference('sup-', [status(thm)], ['14', '15'])).
% 9.46/9.66  thf('52', plain,
% 9.46/9.66      (![X5 : $i, X7 : $i]:
% 9.46/9.66         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 9.46/9.66      inference('cnf', [status(esa)], [d3_tarski])).
% 9.46/9.66  thf('53', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 9.46/9.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.46/9.66  thf('54', plain,
% 9.46/9.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.46/9.66         (~ (r2_hidden @ X25 @ X26)
% 9.46/9.66          | (r2_hidden @ X25 @ X27)
% 9.46/9.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 9.46/9.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 9.46/9.66  thf('55', plain,
% 9.46/9.66      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 9.46/9.66      inference('sup-', [status(thm)], ['53', '54'])).
% 9.46/9.66  thf('56', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['52', '55'])).
% 9.46/9.66  thf('57', plain,
% 9.46/9.66      (![X5 : $i, X7 : $i]:
% 9.46/9.66         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 9.46/9.66      inference('cnf', [status(esa)], [d3_tarski])).
% 9.46/9.66  thf('58', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 9.46/9.66      inference('sup-', [status(thm)], ['56', '57'])).
% 9.46/9.66  thf('59', plain, ((r1_tarski @ sk_B @ sk_A)),
% 9.46/9.66      inference('simplify', [status(thm)], ['58'])).
% 9.46/9.66  thf('60', plain,
% 9.46/9.66      (![X8 : $i, X9 : $i]:
% 9.46/9.66         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 9.46/9.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 9.46/9.66  thf('61', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 9.46/9.66      inference('sup-', [status(thm)], ['59', '60'])).
% 9.46/9.66  thf(t49_xboole_1, axiom,
% 9.46/9.66    (![A:$i,B:$i,C:$i]:
% 9.46/9.66     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 9.46/9.66       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 9.46/9.66  thf('62', plain,
% 9.46/9.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 9.46/9.66         ((k3_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 9.46/9.66           = (k4_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14))),
% 9.46/9.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 9.46/9.66  thf('63', plain,
% 9.46/9.66      (![X0 : $i]:
% 9.46/9.66         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 9.46/9.66           = (k4_xboole_0 @ sk_B @ X0))),
% 9.46/9.66      inference('sup+', [status(thm)], ['61', '62'])).
% 9.46/9.66  thf('64', plain,
% 9.46/9.66      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 9.46/9.66         = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 9.46/9.66      inference('sup+', [status(thm)], ['51', '63'])).
% 9.46/9.66  thf('65', plain,
% 9.46/9.66      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.46/9.66      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.46/9.66  thf('66', plain,
% 9.46/9.66      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))
% 9.46/9.66         = (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 9.46/9.66      inference('demod', [status(thm)], ['49', '50', '64', '65'])).
% 9.46/9.66  thf('67', plain,
% 9.46/9.66      (((k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 9.46/9.66         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 9.46/9.66      inference('demod', [status(thm)], ['13', '66'])).
% 9.46/9.66  thf('68', plain, ($false),
% 9.46/9.66      inference('simplify_reflect-', [status(thm)], ['8', '67'])).
% 9.46/9.66  
% 9.46/9.66  % SZS output end Refutation
% 9.46/9.66  
% 9.46/9.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
