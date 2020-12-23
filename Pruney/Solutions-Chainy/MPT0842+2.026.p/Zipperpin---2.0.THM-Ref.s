%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5JZ12QfEA

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:28 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 187 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  912 (3011 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k8_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k10_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k10_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_2 @ X24 @ X22 @ X23 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
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
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
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
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
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
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('27',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k10_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( sk_D_2 @ X24 @ X22 @ X23 ) @ X22 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( m1_subset_1 @ sk_F @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('41',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
    | ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ X29 ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('45',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X21 ) @ X24 )
      | ~ ( r2_hidden @ X21 @ ( k2_relat_1 @ X24 ) )
      | ( r2_hidden @ X23 @ ( k10_relat_1 @ X24 @ X22 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['14','15'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ( X15
       != ( k2_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ ( k2_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ ( k2_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['49','50','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k10_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k10_relat_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_F ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','43','44','45','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H5JZ12QfEA
% 0.16/0.36  % Computer   : n019.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 12:15:53 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 407 iterations in 0.482s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.76/0.96  thf(sk_F_type, type, sk_F: $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.96  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.96  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.76/0.96  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(t53_relset_1, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.76/0.96               ( ![D:$i]:
% 0.76/0.96                 ( ( m1_subset_1 @
% 0.76/0.96                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.76/0.96                   ( ![E:$i]:
% 0.76/0.96                     ( ( m1_subset_1 @ E @ A ) =>
% 0.76/0.96                       ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.76/0.96                         ( ?[F:$i]:
% 0.76/0.96                           ( ( r2_hidden @ F @ B ) & 
% 0.76/0.96                             ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.76/0.96                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.96              ( ![C:$i]:
% 0.76/0.96                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.76/0.96                  ( ![D:$i]:
% 0.76/0.96                    ( ( m1_subset_1 @
% 0.76/0.96                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.76/0.96                      ( ![E:$i]:
% 0.76/0.96                        ( ( m1_subset_1 @ E @ A ) =>
% 0.76/0.96                          ( ( r2_hidden @ E @ ( k8_relset_1 @ A @ C @ D @ B ) ) <=>
% 0.76/0.96                            ( ?[F:$i]:
% 0.76/0.96                              ( ( r2_hidden @ F @ B ) & 
% 0.76/0.96                                ( r2_hidden @ ( k4_tarski @ E @ F ) @ D ) & 
% 0.76/0.96                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t53_relset_1])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)
% 0.76/0.96        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)) | 
% 0.76/0.96       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (((m1_subset_1 @ sk_F @ sk_C_1)
% 0.76/0.96        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 0.76/0.96       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['2'])).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k8_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.76/0.96          | ((k8_relset_1 @ X26 @ X27 @ X25 @ X28) = (k10_relat_1 @ X25 @ X28)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 0.76/0.96           = (k10_relat_1 @ sk_D_3 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (((r2_hidden @ sk_F @ sk_B)
% 0.76/0.96        | (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['7'])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '8'])).
% 0.76/0.96  thf(t166_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ C ) =>
% 0.76/0.96       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.76/0.96         ( ?[D:$i]:
% 0.76/0.96           ( ( r2_hidden @ D @ B ) & 
% 0.76/0.96             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.76/0.96             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X23 @ (k10_relat_1 @ X24 @ X22))
% 0.76/0.96          | (r2_hidden @ (k4_tarski @ X23 @ (sk_D_2 @ X24 @ X22 @ X23)) @ X24)
% 0.76/0.96          | ~ (v1_relat_1 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.96         | (r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.76/0.96            sk_D_3)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(cc2_relat_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.76/0.96          | (v1_relat_1 @ X10)
% 0.76/0.96          | ~ (v1_relat_1 @ X11))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) | (v1_relat_1 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.96  thf(fc6_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.96  thf('16', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.76/0.96         sk_D_3))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['11', '16'])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(l3_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X5 @ X6)
% 0.76/0.96          | (r2_hidden @ X5 @ X7)
% 0.76/0.96          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.76/0.96      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))
% 0.76/0.96          | ~ (r2_hidden @ X0 @ sk_D_3))),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.76/0.96         (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['17', '20'])).
% 0.76/0.96  thf(l54_zfmisc_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.96     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.76/0.96       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.96         ((r2_hidden @ X2 @ X3)
% 0.76/0.96          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.76/0.96      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf(t1_subset, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.76/0.96      inference('cnf', [status(esa)], [t1_subset])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E)) @ 
% 0.76/0.96         sk_D_3))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['11', '16'])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (![X29 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96          | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96          | ~ (r2_hidden @ X29 @ sk_B)
% 0.76/0.96          | ~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      ((![X29 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (((~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)
% 0.76/0.96         | ~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.76/0.96             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['26', '28'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup+', [status(thm)], ['6', '8'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X23 @ (k10_relat_1 @ X24 @ X22))
% 0.76/0.96          | (r2_hidden @ (sk_D_2 @ X24 @ X22 @ X23) @ X22)
% 0.76/0.96          | ~ (v1_relat_1 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.96         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.96  thf('33', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 0.76/0.96         <= (((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.76/0.96             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['29', '34'])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))) | 
% 0.76/0.96       ~
% 0.76/0.96       (![X29 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96           | ~ (r2_hidden @ X29 @ sk_B)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['25', '35'])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 0.76/0.96      inference('split', [status(esa)], ['2'])).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['7'])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      ((![X29 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['27'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.76/0.96             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.96  thf('42', plain,
% 0.76/0.96      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 0.76/0.96         <= ((![X29 : $i]:
% 0.76/0.96                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96                 | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.76/0.96             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.76/0.96             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['38', '41'])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)) | 
% 0.76/0.96       ~
% 0.76/0.96       (![X29 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.76/0.96       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['37', '42'])).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      (~ ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))) | 
% 0.76/0.96       (![X29 : $i]:
% 0.76/0.96          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.76/0.96           | ~ (r2_hidden @ (k4_tarski @ sk_E @ X29) @ sk_D_3)
% 0.76/0.96           | ~ (r2_hidden @ X29 @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['27'])).
% 0.76/0.96  thf('45', plain,
% 0.76/0.96      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.76/0.96       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['7'])).
% 0.76/0.96  thf('46', plain,
% 0.76/0.96      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['7'])).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf('48', plain,
% 0.76/0.96      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X21 @ X22)
% 0.76/0.96          | ~ (r2_hidden @ (k4_tarski @ X23 @ X21) @ X24)
% 0.76/0.96          | ~ (r2_hidden @ X21 @ (k2_relat_1 @ X24))
% 0.76/0.96          | (r2_hidden @ X23 @ (k10_relat_1 @ X24 @ X22))
% 0.76/0.96          | ~ (v1_relat_1 @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      ((![X0 : $i]:
% 0.76/0.96          (~ (v1_relat_1 @ sk_D_3)
% 0.76/0.96           | (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 0.76/0.96           | ~ (r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3))
% 0.76/0.96           | ~ (r2_hidden @ sk_F @ X0)))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.96  thf('50', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('split', [status(esa)], ['0'])).
% 0.76/0.96  thf(d5_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.76/0.96       ( ![C:$i]:
% 0.76/0.96         ( ( r2_hidden @ C @ B ) <=>
% 0.76/0.96           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.76/0.96         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.76/0.96          | (r2_hidden @ X13 @ X15)
% 0.76/0.96          | ((X15) != (k2_relat_1 @ X14)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.76/0.96  thf('53', plain,
% 0.76/0.96      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.76/0.96         ((r2_hidden @ X13 @ (k2_relat_1 @ X14))
% 0.76/0.96          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14))),
% 0.76/0.96      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.96  thf('54', plain,
% 0.76/0.96      (((r2_hidden @ sk_F @ (k2_relat_1 @ sk_D_3)))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['51', '53'])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      ((![X0 : $i]:
% 0.76/0.96          ((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ X0))
% 0.76/0.96           | ~ (r2_hidden @ sk_F @ X0)))
% 0.76/0.96         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('demod', [status(thm)], ['49', '50', '54'])).
% 0.76/0.96  thf('56', plain,
% 0.76/0.96      (((r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.76/0.96             ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['46', '55'])).
% 0.76/0.96  thf('57', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ X0)
% 0.76/0.96           = (k10_relat_1 @ sk_D_3 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      ((~ (r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['27'])).
% 0.76/0.96  thf('59', plain,
% 0.76/0.96      ((~ (r2_hidden @ sk_E @ (k10_relat_1 @ sk_D_3 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.96  thf('60', plain,
% 0.76/0.96      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.76/0.96       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_F) @ sk_D_3)) | 
% 0.76/0.96       ((r2_hidden @ sk_E @ (k8_relset_1 @ sk_A @ sk_C_1 @ sk_D_3 @ sk_B)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['56', '59'])).
% 0.76/0.96  thf('61', plain, ($false),
% 0.76/0.96      inference('sat_resolution*', [status(thm)],
% 0.76/0.96                ['1', '3', '36', '43', '44', '45', '60'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
