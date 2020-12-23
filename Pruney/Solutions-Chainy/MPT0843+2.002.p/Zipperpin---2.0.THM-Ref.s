%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ycjWaoW5Qe

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 (1183 expanded)
%              Number of leaves         :   24 ( 345 expanded)
%              Depth                    :   26
%              Number of atoms          : 1252 (20317 expanded)
%              Number of equality atoms :   28 ( 493 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ X15 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ X0 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('7',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X24: $i] :
      ( ( ( k11_relat_1 @ sk_B @ X24 )
        = ( k11_relat_1 @ sk_C @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) )
      = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_C = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) )
      = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ X0 @ sk_A @ sk_A ) ) @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ X0 @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ X0 @ sk_A @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('22',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['15','36'])).

thf('38',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) )
      = ( k11_relat_1 @ sk_C @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['9','14'])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_C )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ X14 @ X17 @ X16 @ X15 ) @ ( sk_F @ X14 @ X17 @ X16 @ X15 ) ) @ X14 )
      | ( r2_relset_1 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_relset_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( k11_relat_1 @ sk_B @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('53',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k11_relat_1 @ X9 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E @ sk_B @ sk_C @ sk_A @ sk_A ) @ ( sk_F @ sk_B @ sk_C @ sk_A @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( sk_C = sk_B )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_C = sk_B )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('65',plain,
    ( ( sk_C = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','71'])).

thf('73',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['0','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','71'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('79',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('82',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','82'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['68','70'])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','71'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','71'])).

thf('87',plain,(
    r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['83','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ycjWaoW5Qe
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 140 iterations in 0.086s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t54_relset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.53           ( ( ![D:$i]:
% 0.20/0.53               ( ( r2_hidden @ D @ A ) =>
% 0.20/0.53                 ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.53             ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.53          ( ![C:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.53              ( ( ![D:$i]:
% 0.20/0.53                  ( ( r2_hidden @ D @ A ) =>
% 0.20/0.53                    ( ( k11_relat_1 @ B @ D ) = ( k11_relat_1 @ C @ D ) ) ) ) =>
% 0.20/0.53                ( r2_relset_1 @ A @ A @ B @ C ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t54_relset_1])).
% 0.20/0.53  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d3_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53           ( ( r2_relset_1 @ A @ B @ C @ D ) <=>
% 0.20/0.53             ( ![E:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.53                 ( ![F:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.53                     ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ C ) <=>
% 0.20/0.53                       ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.53          | (m1_subset_1 @ (sk_E @ X14 @ X17 @ X16 @ X15) @ X15)
% 0.20/0.53          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.20/0.53          | (m1_subset_1 @ (sk_E @ sk_B @ X0 @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A)
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf(d2_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X1 @ X2)
% 0.20/0.53          | (r2_hidden @ X1 @ X2)
% 0.20/0.53          | (v1_xboole_0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (v1_xboole_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X24 : $i]:
% 0.20/0.53         (((k11_relat_1 @ sk_B @ X24) = (k11_relat_1 @ sk_C @ X24))
% 0.20/0.53          | ~ (r2_hidden @ X24 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_A)
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ((k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))
% 0.20/0.53            = (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.53          | ((X20) = (X23))
% 0.20/0.53          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 0.20/0.53          | ((sk_C) = (X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      ((((sk_C) = (sk_B)) | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))
% 0.20/0.53          = (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (v1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['9', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.53              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.53             X17)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.53              (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.53             X14)
% 0.20/0.53          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.53          | (r2_relset_1 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ sk_B @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.53              (sk_F @ sk_B @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.53             sk_B)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ sk_B @ X0 @ sk_A @ sk_A) @ 
% 0.20/0.53              (sk_F @ sk_B @ X0 @ sk_A @ sk_A)) @ 
% 0.20/0.53             X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (((r2_hidden @ 
% 0.20/0.53         (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53          (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.53         sk_C)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.53           sk_B)
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.53  thf(t204_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.53         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.53          | (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.53           sk_B)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.53          | (v1_relat_1 @ X4)
% 0.20/0.53          | ~ (v1_relat_1 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.53           sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.53          | (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53         (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.53          | (v1_relat_1 @ X4)
% 0.20/0.53          | ~ (v1_relat_1 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53         (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53         (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (v1_xboole_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (v1_xboole_0 @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))
% 0.20/0.53          = (k11_relat_1 @ sk_C @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53        | (v1_xboole_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['9', '14'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ 
% 0.20/0.53             (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53          | (v1_xboole_0 @ sk_A)
% 0.20/0.53          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.53  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ 
% 0.20/0.53             (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A)))
% 0.20/0.53          | (v1_xboole_0 @ sk_A)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ X0) @ sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((v1_xboole_0 @ sk_A)
% 0.20/0.53        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.53            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.53           sk_C)
% 0.20/0.53        | (v1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((r2_hidden @ 
% 0.20/0.54         (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54          (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54         sk_C)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (v1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.54          | ~ (r2_hidden @ 
% 0.20/0.54               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.54                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.54               X17)
% 0.20/0.54          | ~ (r2_hidden @ 
% 0.20/0.54               (k4_tarski @ (sk_E @ X14 @ X17 @ X16 @ X15) @ 
% 0.20/0.54                (sk_F @ X14 @ X17 @ X16 @ X15)) @ 
% 0.20/0.54               X14)
% 0.20/0.54          | (r2_relset_1 @ X15 @ X16 @ X17 @ X14)
% 0.20/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_relset_1])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ~ (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54              (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54             sk_B)
% 0.20/0.54        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ~ (r2_hidden @ 
% 0.20/0.54             (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54              (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54             sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((~ (r2_hidden @ 
% 0.20/0.54           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54           sk_B)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (v1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ (sk_F @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54           (k11_relat_1 @ sk_B @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X8 @ (k11_relat_1 @ X9 @ X10))
% 0.20/0.54          | (r2_hidden @ (k4_tarski @ X10 @ X8) @ X9)
% 0.20/0.54          | ~ (v1_relat_1 @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54           sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A)
% 0.20/0.54        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k4_tarski @ (sk_E @ sk_B @ sk_C @ sk_A @ sk_A) @ 
% 0.20/0.54            (sk_F @ sk_B @ sk_C @ sk_A @ sk_A)) @ 
% 0.20/0.54           sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_A) | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('clc', [status(thm)], ['51', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((((sk_C) = (sk_B)) | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.54  thf('59', plain, (((v1_xboole_0 @ sk_A) | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc3_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54       ( ![C:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54           ( v1_xboole_0 @ C ) ) ) ))).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ X11)
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 0.20/0.54          | (v1_xboole_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.20/0.54  thf('62', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain, ((((sk_C) = (sk_B)) | (v1_xboole_0 @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['59', '62'])).
% 0.20/0.54  thf(t6_boole, axiom,
% 0.20/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t6_boole])).
% 0.20/0.54  thf('65', plain, ((((sk_C) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.54  thf('66', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.54          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.20/0.54          | ((X20) != (X23)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.54         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.54  thf('71', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.54  thf('72', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['67', '71'])).
% 0.20/0.54  thf('73', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['0', '72'])).
% 0.20/0.54  thf('74', plain, (((v1_xboole_0 @ sk_A) | ((sk_C) = (sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['67', '71'])).
% 0.20/0.54  thf('76', plain, (((v1_xboole_0 @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ X11)
% 0.20/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 0.20/0.54          | (v1_xboole_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.20/0.54  thf('79', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.54  thf('80', plain, ((((sk_C) = (k1_xboole_0)) | (v1_xboole_0 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['76', '79'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t6_boole])).
% 0.20/0.54  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.54      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['73', '82'])).
% 0.20/0.54  thf('84', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.54      inference('sup-', [status(thm)], ['68', '70'])).
% 0.20/0.54  thf('85', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['67', '71'])).
% 0.20/0.54  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['67', '71'])).
% 0.20/0.54  thf('87', plain, ((r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.20/0.54  thf('88', plain, ($false), inference('demod', [status(thm)], ['83', '87'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
