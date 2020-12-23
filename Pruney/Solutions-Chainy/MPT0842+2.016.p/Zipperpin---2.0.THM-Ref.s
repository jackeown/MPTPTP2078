%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vgaNKn457B

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 213 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  968 (3225 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) ) )
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D @ X15 @ X13 @ X14 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X26 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('40',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('49',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
    | ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X26 ) @ sk_D_1 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('53',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X15 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X15 ) )
      | ( r2_hidden @ X14 @ ( k10_relat_1 @ X15 @ X13 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('61',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['35'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','51','52','53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vgaNKn457B
% 0.12/0.35  % Computer   : n003.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 12:45:57 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.22/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 81 iterations in 0.028s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.47  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(t53_relset_1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.47               ( ![D:$i]:
% 0.22/0.47                 ( ( m1_subset_1 @
% 0.22/0.47                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.22/0.47                   ( ![E:$i]:
% 0.22/0.47                     ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.47                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.22/0.47                         ( ?[F:$i]:
% 0.22/0.47                           ( ( r2_hidden @ F @ B ) & 
% 0.22/0.47                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.22/0.47                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.47              ( ![C:$i]:
% 0.22/0.47                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.47                  ( ![D:$i]:
% 0.22/0.47                    ( ( m1_subset_1 @
% 0.22/0.47                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.22/0.47                      ( ![E:$i]:
% 0.22/0.47                        ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.47                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.22/0.47                            ( ?[F:$i]:
% 0.22/0.47                              ( ( r2_hidden @ F @ B ) & 
% 0.22/0.47                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.22/0.47                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)
% 0.22/0.47        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.22/0.47       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (((m1_subset_1 @ sk_F @ sk_C)
% 0.22/0.47        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.22/0.47       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['2'])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.47          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.22/0.47           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (((r2_hidden @ sk_F @ sk_B)
% 0.22/0.47        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['6', '8'])).
% 0.22/0.47  thf(t166_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.22/0.47         ( ?[D:$i]:
% 0.22/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.47             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.22/0.47             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k2_relat_1 @ X15))
% 0.22/0.47          | ~ (v1_relat_1 @ X15))),
% 0.22/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1))))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(cc2_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.47          | (v1_relat_1 @ X6)
% 0.22/0.47          | ~ (v1_relat_1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(fc6_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.47  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ (k2_relat_1 @ sk_D_1)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('demod', [status(thm)], ['11', '16'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(cc2_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.47         ((v5_relat_1 @ X19 @ X21)
% 0.22/0.47          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.47  thf('20', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf(d19_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i]:
% 0.22/0.47         (~ (v5_relat_1 @ X8 @ X9)
% 0.22/0.47          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.22/0.47          | ~ (v1_relat_1 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.47  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 0.22/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.47  thf(t3_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (![X0 : $i, X2 : $i]:
% 0.22/0.47         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.47  thf(t4_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.47          | (m1_subset_1 @ X3 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((m1_subset_1 @ X0 @ sk_C)
% 0.22/0.47          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['17', '28'])).
% 0.22/0.47  thf('30', plain,
% 0.22/0.47      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['6', '8'])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D @ X15 @ X13 @ X14)) @ X15)
% 0.22/0.47          | ~ (v1_relat_1 @ X15))),
% 0.22/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.47  thf('32', plain,
% 0.22/0.47      (((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.22/0.47            sk_D_1)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.47  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D @ sk_D_1 @ sk_B @ sk_E)) @ 
% 0.22/0.47         sk_D_1))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.47  thf('35', plain,
% 0.22/0.47      (![X26 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47          | ~ (r2_hidden @ X26 @ sk_B)
% 0.22/0.47          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      ((![X26 : $i]:
% 0.22/0.47          (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47           | ~ (r2_hidden @ X26 @ sk_B)))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['35'])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.22/0.47         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))) & 
% 0.22/0.47             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['34', '36'])).
% 0.22/0.47  thf('38', plain,
% 0.22/0.47      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['6', '8'])).
% 0.22/0.47  thf('39', plain,
% 0.22/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.22/0.47          | ~ (v1_relat_1 @ X15))),
% 0.22/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.47  thf('40', plain,
% 0.22/0.47      (((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.47  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('42', plain,
% 0.22/0.47      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.22/0.47         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.47  thf('43', plain,
% 0.22/0.47      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))) & 
% 0.22/0.47             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('demod', [status(thm)], ['37', '42'])).
% 0.22/0.47  thf('44', plain,
% 0.22/0.47      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.22/0.47       ~
% 0.22/0.47       (![X26 : $i]:
% 0.22/0.47          (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47           | ~ (r2_hidden @ X26 @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['29', '43'])).
% 0.22/0.47  thf('45', plain,
% 0.22/0.47      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.22/0.47      inference('split', [status(esa)], ['2'])).
% 0.22/0.47  thf('46', plain,
% 0.22/0.47      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('47', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('48', plain,
% 0.22/0.47      ((![X26 : $i]:
% 0.22/0.47          (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47           | ~ (r2_hidden @ X26 @ sk_B)))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['35'])).
% 0.22/0.47  thf('49', plain,
% 0.22/0.47      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))) & 
% 0.22/0.47             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.47  thf('50', plain,
% 0.22/0.47      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.22/0.47         <= ((![X26 : $i]:
% 0.22/0.47                (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47                 | ~ (r2_hidden @ X26 @ sk_B))) & 
% 0.22/0.47             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.22/0.47             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['46', '49'])).
% 0.22/0.47  thf('51', plain,
% 0.22/0.47      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.22/0.47       ~
% 0.22/0.47       (![X26 : $i]:
% 0.22/0.47          (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.22/0.47       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['45', '50'])).
% 0.22/0.47  thf('52', plain,
% 0.22/0.47      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))) | 
% 0.22/0.47       (![X26 : $i]:
% 0.22/0.47          (~ (m1_subset_1 @ X26 @ sk_C)
% 0.22/0.47           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X26) @ sk_D_1)
% 0.22/0.47           | ~ (r2_hidden @ X26 @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['35'])).
% 0.22/0.47  thf('53', plain,
% 0.22/0.47      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.22/0.47       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('54', plain,
% 0.22/0.47      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.22/0.47      inference('split', [status(esa)], ['7'])).
% 0.22/0.47  thf('55', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('56', plain,
% 0.22/0.47      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X15)
% 0.22/0.47          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X15))
% 0.22/0.47          | (r2_hidden @ X14 @ (k10_relat_1 @ X15 @ X13))
% 0.22/0.47          | ~ (v1_relat_1 @ X15))),
% 0.22/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.22/0.47  thf('57', plain,
% 0.22/0.47      ((![X0 : $i]:
% 0.22/0.47          (~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.22/0.47           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))
% 0.22/0.47           | ~ (r2_hidden @ sk_F @ X0)))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.47  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('59', plain,
% 0.22/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf(t20_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.22/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.47           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.22/0.47  thf('60', plain,
% 0.22/0.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.47         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.22/0.47          | (r2_hidden @ X17 @ (k2_relat_1 @ X18))
% 0.22/0.47          | ~ (v1_relat_1 @ X18))),
% 0.22/0.47      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.22/0.47  thf('61', plain,
% 0.22/0.47      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1))))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.47  thf('62', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('63', plain,
% 0.22/0.47      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_1)))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.47  thf('64', plain,
% 0.22/0.47      ((![X0 : $i]:
% 0.22/0.47          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ X0))
% 0.22/0.47           | ~ (r2_hidden @ sk_F @ X0)))
% 0.22/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('demod', [status(thm)], ['57', '58', '63'])).
% 0.22/0.47  thf('65', plain,
% 0.22/0.47      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.22/0.47             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['54', '64'])).
% 0.22/0.47  thf('66', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ X0)
% 0.22/0.47           = (k10_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('67', plain,
% 0.22/0.47      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (~
% 0.22/0.47             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('split', [status(esa)], ['35'])).
% 0.22/0.47  thf('68', plain,
% 0.22/0.47      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_1 @ sk_B)))
% 0.22/0.47         <= (~
% 0.22/0.47             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.47  thf('69', plain,
% 0.22/0.47      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.22/0.47       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_1)) | 
% 0.22/0.47       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C @ sk_D_1 @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['65', '68'])).
% 0.22/0.47  thf('70', plain, ($false),
% 0.22/0.47      inference('sat_resolution*', [status(thm)],
% 0.22/0.47                ['1', '3', '44', '51', '52', '53', '69'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
