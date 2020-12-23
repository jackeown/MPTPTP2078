%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nu9O3z1UBD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:29 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 198 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  935 (3136 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t53_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ E @ F ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k8_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k10_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( sk_D @ X17 @ X15 @ X16 ) ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X25 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D @ X17 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) )
   <= ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('41',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X25: $i] :
          ( ~ ( m1_subset_1 @ X25 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X25 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X25: $i] :
        ( ~ ( m1_subset_1 @ X25 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X25 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X25 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('45',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X17 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X16 @ ( k10_relat_1 @ X17 @ X15 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X19 @ ( k2_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('54',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('56',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','43','44','45','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nu9O3z1UBD
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1074 iterations in 0.674s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.13  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.13  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.13  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.13  thf(sk_F_type, type, sk_F: $i).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(t53_relset_1, conjecture,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.13           ( ![C:$i]:
% 0.90/1.13             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.13               ( ![D:$i]:
% 0.90/1.13                 ( ( m1_subset_1 @
% 0.90/1.13                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.90/1.13                   ( ![E:$i]:
% 0.90/1.13                     ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.13                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.90/1.13                         ( ?[F:$i]:
% 0.90/1.13                           ( ( r2_hidden @ F @ B ) & 
% 0.90/1.13                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.90/1.13                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i]:
% 0.90/1.13        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.13          ( ![B:$i]:
% 0.90/1.13            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.13              ( ![C:$i]:
% 0.90/1.13                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.13                  ( ![D:$i]:
% 0.90/1.13                    ( ( m1_subset_1 @
% 0.90/1.13                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.90/1.13                      ( ![E:$i]:
% 0.90/1.13                        ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.13                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.90/1.13                            ( ?[F:$i]:
% 0.90/1.13                              ( ( r2_hidden @ F @ B ) & 
% 0.90/1.13                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.90/1.13                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.90/1.13  thf('0', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.90/1.13        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.90/1.13       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_F @ sk_C)
% 0.90/1.13        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.90/1.13       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['2'])).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k8_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.90/1.13          | ((k8_relset_1 @ X22 @ X23 @ X21 @ X24) = (k10_relat_1 @ X21 @ X24)))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.90/1.13           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (((r2_hidden @ sk_F @ sk_B)
% 0.90/1.13        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('8', plain,
% 0.90/1.13      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('split', [status(esa)], ['7'])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup+', [status(thm)], ['6', '8'])).
% 0.90/1.13  thf(t166_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ C ) =>
% 0.90/1.13       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.90/1.13         ( ?[D:$i]:
% 0.90/1.13           ( ( r2_hidden @ D @ B ) & 
% 0.90/1.13             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.90/1.13             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.90/1.13          | (r2_hidden @ (k4_tarski @ X16 @ (sk_D @ X17 @ X15 @ X16)) @ X17)
% 0.90/1.13          | ~ (v1_relat_1 @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (((~ (v1_relat_1 @ sk_D_1)
% 0.90/1.13         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.90/1.13            sk_D_1)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(cc2_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.90/1.13          | (v1_relat_1 @ X10)
% 0.90/1.13          | ~ (v1_relat_1 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf(fc6_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.90/1.13      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.90/1.13  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.90/1.13         sk_D_1))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('demod', [status(thm)], ['11', '16'])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(l3_subset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.13       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X5 @ X6)
% 0.90/1.13          | (r2_hidden @ X5 @ X7)
% 0.90/1.13          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.90/1.13      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.90/1.13  thf('20', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.90/1.13          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['18', '19'])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.90/1.13         (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['17', '20'])).
% 0.90/1.13  thf(l54_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.90/1.13       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.13         ((r2_hidden @ X2 @ X3)
% 0.90/1.13          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.90/1.13      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf(t1_subset, axiom,
% 0.90/1.13    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.90/1.13         sk_D_1))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('demod', [status(thm)], ['11', '16'])).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X25 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13          | ~ (r2_hidden @ X25 @ sk_B)
% 0.90/1.13          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      ((![X25 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.90/1.13      inference('split', [status(esa)], ['27'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.90/1.13         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.13             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup+', [status(thm)], ['6', '8'])).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.90/1.13          | (r2_hidden @ (sk_D @ X17 @ X15 @ X16) @ X15)
% 0.90/1.13          | ~ (v1_relat_1 @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      (((~ (v1_relat_1 @ sk_D_1)
% 0.90/1.13         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.13  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.90/1.13         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('demod', [status(thm)], ['32', '33'])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.13             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('demod', [status(thm)], ['29', '34'])).
% 0.90/1.13  thf('36', plain,
% 0.90/1.13      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.90/1.13       ~
% 0.90/1.13       (![X25 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13           | ~ (r2_hidden @ X25 @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['25', '35'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.90/1.13      inference('split', [status(esa)], ['2'])).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['7'])).
% 0.90/1.13  thf('39', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('40', plain,
% 0.90/1.13      ((![X25 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13           | ~ (r2_hidden @ X25 @ sk_B)))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))))),
% 0.90/1.13      inference('split', [status(esa)], ['27'])).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.13             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.13  thf('42', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.90/1.13         <= ((![X25 : $i]:
% 0.90/1.13                (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13                 | ~ (r2_hidden @ X25 @ sk_B))) & 
% 0.90/1.13             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.90/1.13             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['38', '41'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.90/1.13       ~
% 0.90/1.13       (![X25 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13           | ~ (r2_hidden @ X25 @ sk_B))) | 
% 0.90/1.13       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '42'])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.90/1.13       (![X25 : $i]:
% 0.90/1.13          (~ (m1_subset_1 @ X25 @ sk_C)
% 0.90/1.13           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X25) @ sk_D_1)
% 0.90/1.13           | ~ (r2_hidden @ X25 @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['27'])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.90/1.13       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['7'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.90/1.13      inference('split', [status(esa)], ['7'])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.13         (~ (r2_hidden @ X14 @ X15)
% 0.90/1.13          | ~ (r2_hidden @ (k4_tarski @ X16 @ X14) @ X17)
% 0.90/1.13          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X17))
% 0.90/1.13          | (r2_hidden @ X16 @ (k10_relat_1 @ X17 @ X15))
% 0.90/1.13          | ~ (v1_relat_1 @ X17))),
% 0.90/1.13      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      ((![X0 : $i]:
% 0.90/1.13          (~ (v1_relat_1 @ sk_D_1)
% 0.90/1.13           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.90/1.13           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.90/1.13           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.13  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('51', plain,
% 0.90/1.13      ((![X0 : $i]:
% 0.90/1.13          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.90/1.13           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.90/1.13           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['49', '50'])).
% 0.90/1.13  thf('52', plain,
% 0.90/1.13      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('split', [status(esa)], ['0'])).
% 0.90/1.13  thf(t20_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ C ) =>
% 0.90/1.13       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.90/1.13         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.90/1.13           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.13         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.90/1.13          | (r2_hidden @ X19 @ (k2_relat_1 @ X20))
% 0.90/1.13          | ~ (v1_relat_1 @ X20))),
% 0.90/1.13      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['52', '53'])).
% 0.90/1.13  thf('55', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.13      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('56', plain,
% 0.90/1.13      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      ((![X0 : $i]:
% 0.90/1.13          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.90/1.13           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.13         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('demod', [status(thm)], ['51', '56'])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.90/1.13             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['46', '57'])).
% 0.90/1.13  thf('59', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.90/1.13           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (~
% 0.90/1.13             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('split', [status(esa)], ['27'])).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.90/1.13         <= (~
% 0.90/1.13             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.13  thf('62', plain,
% 0.90/1.13      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.90/1.13       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.90/1.13       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['58', '61'])).
% 0.90/1.13  thf('63', plain, ($false),
% 0.90/1.13      inference('sat_resolution*', [status(thm)],
% 0.90/1.13                ['1', '3', '36', '43', '44', '45', '62'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
