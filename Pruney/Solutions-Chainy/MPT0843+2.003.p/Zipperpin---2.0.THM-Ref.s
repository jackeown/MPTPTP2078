%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjO8QS6zmx

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 244 expanded)
%              Number of leaves         :   20 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  927 (4115 expanded)
%              Number of equality atoms :    5 (  72 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t54_relset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ( k11_relat_1 @ B @ D )
                  = ( k11_relat_1 @ C @ D ) ) )
           => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( ( k11_relat_1 @ B @ D )
                    = ( k11_relat_1 @ C @ D ) ) )
             => ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ! [D: $i] :
          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( r2_relset_1 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ C )
                    <=> ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X15 @ X18 @ X17 @ X16 ) @ ( sk_F @ X15 @ X18 @ X17 @ X16 ) ) @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X15 @ X18 @ X17 @ X16 ) @ ( sk_F @ X15 @ X18 @ X17 @ X16 ) ) @ X15 )
      | ( r2_relset_1 @ X16 @ X17 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ X0 @ sk_A @ sk_A ) ) @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ X0 @ sk_A @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['27','30'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('33',plain,(
    r2_hidden @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X21 )
        = ( k11_relat_1 @ sk_C @ X21 ) )
      | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) )
    = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) )
    | ( r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('41',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X15 @ X18 @ X17 @ X16 ) @ ( sk_F @ X15 @ X18 @ X17 @ X16 ) ) @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X15 @ X18 @ X17 @ X16 ) @ ( sk_F @ X15 @ X18 @ X17 @ X16 ) ) @ X15 )
      | ( r2_relset_1 @ X16 @ X17 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('50',plain,
    ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) )
    = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E @ sk_C @ sk_B @ sk_A @ sk_A ) @ ( sk_F @ sk_C @ sk_B @ sk_A @ sk_A ) ) @ sk_C ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['48','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjO8QS6zmx
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 77 iterations in 0.056s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(t54_relset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.52           ( ( ![D:$i]:
% 0.20/0.52               ( ( r2_hidden @ D @ A ) =>
% 0.20/0.52                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.52             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.52              ( ( ![D:$i]:
% 0.20/0.52                  ( ( r2_hidden @ D @ A ) =>
% 0.20/0.52                    ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.52                ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t54_relset_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ![D:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52           ( ( r2_relset_1 @ A @ B @ C @ D ) <=>
% 0.20/0.52             ( ![E:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.52                 ( ![F:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.52                     ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ C ) <=>
% 0.20/0.52                       ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ X15 @ X18 @ X17 @ X16) @ 
% 0.20/0.52              (sk_F @ X15 @ X18 @ X17 @ X16)) @ 
% 0.20/0.52             X18)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ X15 @ X18 @ X17 @ X16) @ 
% 0.20/0.52              (sk_F @ X15 @ X18 @ X17 @ X16)) @ 
% 0.20/0.52             X15)
% 0.20/0.52          | (r2_relset_1 @ X16 @ X17 @ X18 @ X15)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.52          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.52              (sk_F @ sk_C @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.52             sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.52              (sk_F @ sk_C @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.52             X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_B)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52           sk_C)
% 0.20/0.52        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.52  thf('5', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_C)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52           sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf(t204_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ C ) =>
% 0.20/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.52          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_B)
% 0.20/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52        | (r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc2_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.52          | (v1_relat_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf(fc6_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_B)
% 0.20/0.52        | (r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.52          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))
% 0.20/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.52        | (r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.52          | (v1_relat_1 @ X8)
% 0.20/0.52          | ~ (v1_relat_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.52  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (((r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))
% 0.20/0.52        | (r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['16', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_C)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52           sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.52          | (r2_hidden @ X5 @ X7)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (((r2_hidden @ 
% 0.20/0.52         (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52          (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52         sk_B)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52           (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.52          | (r2_hidden @ X5 @ X7)
% 0.20/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52        (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['27', '30'])).
% 0.20/0.52  thf(l54_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.52  thf('33', plain, ((r2_hidden @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X21 : $i]:
% 0.20/0.52         (((k11_relat_1 @ sk_B @ X21) = (k11_relat_1 @ sk_C @ X21))
% 0.20/0.52          | ~ (r2_hidden @ X21 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))
% 0.20/0.52         = (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))
% 0.20/0.52        | (r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52        (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.52        | (r2_hidden @ 
% 0.20/0.52           (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52            (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52           sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52        sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (k4_tarski @ (sk_E @ X15 @ X18 @ X17 @ X16) @ 
% 0.20/0.52                (sk_F @ X15 @ X18 @ X17 @ X16)) @ 
% 0.20/0.52               X18)
% 0.20/0.52          | ~ (r2_hidden @ 
% 0.20/0.52               (k4_tarski @ (sk_E @ X15 @ X18 @ X17 @ X16) @ 
% 0.20/0.52                (sk_F @ X15 @ X18 @ X17 @ X16)) @ 
% 0.20/0.52               X15)
% 0.20/0.52          | (r2_relset_1 @ X16 @ X17 @ X18 @ X15)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.52        | (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.52        | ~ (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52              (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52             sk_C)
% 0.20/0.52        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.20/0.52        | ~ (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52              (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52             sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf('47', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (~ (r2_hidden @ 
% 0.20/0.52          (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52           (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52          sk_C)),
% 0.20/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      ((r2_hidden @ (sk_F @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52        (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A))
% 0.20/0.52         = (k11_relat_1 @ sk_C @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ 
% 0.20/0.52             (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))
% 0.20/0.52          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ 
% 0.20/0.52             (k11_relat_1 @ sk_B @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A)))
% 0.20/0.52          | (r2_hidden @ 
% 0.20/0.52             (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      ((r2_hidden @ 
% 0.20/0.52        (k4_tarski @ (sk_E @ sk_C @ sk_B @ sk_A @ sk_A) @ 
% 0.20/0.52         (sk_F @ sk_C @ sk_B @ sk_A @ sk_A)) @ 
% 0.20/0.52        sk_C)),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '54'])).
% 0.20/0.52  thf('56', plain, ($false), inference('demod', [status(thm)], ['48', '55'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
