%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fhuaSO7unZ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:24 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t52_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                        <=> ? [F: $i] :
                              ( ( r2_hidden @ F @ B )
                              & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                              & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X24 @ X22 @ X23 ) @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
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
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
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
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
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
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('27',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
      | ~ ( r2_hidden @ X29 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ( r2_hidden @ ( sk_D_2 @ X24 @ X22 @ X23 ) @ X22 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['14','15'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_B @ sk_E ) @ sk_C_1 )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('41',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
          | ~ ( r2_hidden @ X29 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
    | ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_3 )
        | ~ ( r2_hidden @ X29 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('45',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ X23 @ ( k9_relat_1 @ X24 @ X22 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_3 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['14','15'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k1_relat_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('53',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X14 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ),
    inference(demod,[status(thm)],['49','50','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference(split,[status(esa)],['27'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_3 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','36','43','44','45','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fhuaSO7unZ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 426 iterations in 0.477s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.93  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.75/0.93  thf(sk_F_type, type, sk_F: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(sk_E_type, type, sk_E: $i).
% 0.75/0.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.93  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.75/0.93  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.75/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.93  thf(t52_relset_1, conjecture,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.93           ( ![C:$i]:
% 0.75/0.93             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.75/0.93               ( ![D:$i]:
% 0.75/0.93                 ( ( m1_subset_1 @
% 0.75/0.93                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.75/0.93                   ( ![E:$i]:
% 0.75/0.93                     ( ( m1_subset_1 @ E @ A ) =>
% 0.75/0.93                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.75/0.93                         ( ?[F:$i]:
% 0.75/0.93                           ( ( r2_hidden @ F @ B ) & 
% 0.75/0.93                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.75/0.93                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i]:
% 0.75/0.93        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.93          ( ![B:$i]:
% 0.75/0.93            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.93              ( ![C:$i]:
% 0.75/0.93                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.75/0.93                  ( ![D:$i]:
% 0.75/0.93                    ( ( m1_subset_1 @
% 0.75/0.93                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.75/0.93                      ( ![E:$i]:
% 0.75/0.93                        ( ( m1_subset_1 @ E @ A ) =>
% 0.75/0.93                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.75/0.93                            ( ?[F:$i]:
% 0.75/0.93                              ( ( r2_hidden @ F @ B ) & 
% 0.75/0.93                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.75/0.93                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)
% 0.75/0.93        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.75/0.93       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (((m1_subset_1 @ sk_F @ sk_C_1)
% 0.75/0.93        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 0.75/0.93       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['2'])).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k7_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.75/0.93          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.75/0.93           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (((r2_hidden @ sk_F @ sk_B)
% 0.75/0.93        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('split', [status(esa)], ['7'])).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup+', [status(thm)], ['6', '8'])).
% 0.75/0.93  thf(t143_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ C ) =>
% 0.75/0.93       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.75/0.93         ( ?[D:$i]:
% 0.75/0.93           ( ( r2_hidden @ D @ B ) & 
% 0.75/0.93             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.75/0.93             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 0.75/0.93          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X24 @ X22 @ X23) @ X23) @ X24)
% 0.75/0.93          | ~ (v1_relat_1 @ X24))),
% 0.75/0.93      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.93         | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.75/0.93            sk_D_3)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['9', '10'])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc2_relat_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ A ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X10 : $i, X11 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.75/0.93          | (v1_relat_1 @ X10)
% 0.75/0.93          | ~ (v1_relat_1 @ X11))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.93  thf(fc6_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.93  thf('16', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.75/0.93         sk_D_3))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('demod', [status(thm)], ['11', '16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(l3_subset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X5 @ X6)
% 0.75/0.93          | (r2_hidden @ X5 @ X7)
% 0.75/0.93          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 0.75/0.93          | ~ (r2_hidden @ X0 @ sk_D_3))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.75/0.93         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['17', '20'])).
% 0.75/0.93  thf(l54_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.75/0.93       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.75/0.93         ((r2_hidden @ X0 @ X1)
% 0.75/0.93          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.75/0.93      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.93  thf(t1_subset, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_subset])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['23', '24'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_E) @ 
% 0.75/0.93         sk_D_3))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('demod', [status(thm)], ['11', '16'])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X29 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93          | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93          | ~ (r2_hidden @ X29 @ sk_B)
% 0.75/0.93          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      ((![X29 : $i]:
% 0.75/0.93          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.75/0.93      inference('split', [status(esa)], ['27'])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (((~ (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)
% 0.75/0.93         | ~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1)))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.75/0.93             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '28'])).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup+', [status(thm)], ['6', '8'])).
% 0.75/0.93  thf('31', plain,
% 0.75/0.93      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 0.75/0.93          | (r2_hidden @ (sk_D_2 @ X24 @ X22 @ X23) @ X22)
% 0.75/0.93          | ~ (v1_relat_1 @ X24))),
% 0.75/0.93      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (((~ (v1_relat_1 @ sk_D_3)
% 0.75/0.93         | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B)))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.93  thf('33', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_B))
% 0.75/0.93         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_B @ sk_E) @ sk_C_1))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.75/0.93             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('demod', [status(thm)], ['29', '34'])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))) | 
% 0.75/0.93       ~
% 0.75/0.93       (![X29 : $i]:
% 0.75/0.93          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93           | ~ (r2_hidden @ X29 @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '35'])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 0.75/0.93      inference('split', [status(esa)], ['2'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['7'])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      ((![X29 : $i]:
% 0.75/0.93          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93           | ~ (r2_hidden @ X29 @ sk_B)))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))))),
% 0.75/0.93      inference('split', [status(esa)], ['27'])).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.75/0.93             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 0.75/0.93         <= ((![X29 : $i]:
% 0.75/0.93                (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93                 | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93                 | ~ (r2_hidden @ X29 @ sk_B))) & 
% 0.75/0.93             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.75/0.93             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['38', '41'])).
% 0.75/0.93  thf('43', plain,
% 0.75/0.93      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.75/0.93       ~
% 0.75/0.93       (![X29 : $i]:
% 0.75/0.93          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93           | ~ (r2_hidden @ X29 @ sk_B))) | 
% 0.75/0.93       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '42'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))) | 
% 0.75/0.93       (![X29 : $i]:
% 0.75/0.93          (~ (m1_subset_1 @ X29 @ sk_C_1)
% 0.75/0.93           | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_3)
% 0.75/0.93           | ~ (r2_hidden @ X29 @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['27'])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.75/0.93       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['7'])).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.75/0.93      inference('split', [status(esa)], ['7'])).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X21 @ X22)
% 0.75/0.93          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ X24)
% 0.75/0.93          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X24))
% 0.75/0.93          | (r2_hidden @ X23 @ (k9_relat_1 @ X24 @ X22))
% 0.75/0.93          | ~ (v1_relat_1 @ X24))),
% 0.75/0.93      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      ((![X0 : $i]:
% 0.75/0.93          (~ (v1_relat_1 @ sk_D_3)
% 0.75/0.93           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.75/0.93           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3))
% 0.75/0.93           | ~ (r2_hidden @ sk_F @ X0)))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.93  thf('50', plain, ((v1_relat_1 @ sk_D_3)),
% 0.75/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf(d4_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.75/0.93       ( ![C:$i]:
% 0.75/0.93         ( ( r2_hidden @ C @ B ) <=>
% 0.75/0.93           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.75/0.93         (~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14)
% 0.75/0.93          | (r2_hidden @ X12 @ X15)
% 0.75/0.93          | ((X15) != (k1_relat_1 @ X14)))),
% 0.75/0.93      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.75/0.93  thf('53', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         ((r2_hidden @ X12 @ (k1_relat_1 @ X14))
% 0.75/0.93          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ X14))),
% 0.75/0.93      inference('simplify', [status(thm)], ['52'])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_3)))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['51', '53'])).
% 0.75/0.93  thf('55', plain,
% 0.75/0.93      ((![X0 : $i]:
% 0.75/0.93          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ X0))
% 0.75/0.93           | ~ (r2_hidden @ sk_F @ X0)))
% 0.75/0.93         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('demod', [status(thm)], ['49', '50', '54'])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.75/0.93             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['46', '55'])).
% 0.75/0.93  thf('57', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ X0)
% 0.75/0.93           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.93  thf('58', plain,
% 0.75/0.93      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (~
% 0.75/0.93             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('split', [status(esa)], ['27'])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      ((~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_B)))
% 0.75/0.93         <= (~
% 0.75/0.93             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['57', '58'])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.75/0.93       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_3)) | 
% 0.75/0.93       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_3 @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['56', '59'])).
% 0.75/0.93  thf('61', plain, ($false),
% 0.75/0.93      inference('sat_resolution*', [status(thm)],
% 0.75/0.93                ['1', '3', '36', '43', '44', '45', '60'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
