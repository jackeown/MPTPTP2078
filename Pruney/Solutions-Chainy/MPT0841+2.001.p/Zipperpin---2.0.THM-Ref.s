%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f6iu7Be9nN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:22 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 214 expanded)
%              Number of leaves         :   33 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  981 (3390 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
      | ~ ( r2_hidden @ X27 @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C ) )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_B )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_D_1 )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('36',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_C ) @ sk_D_1 )
    = sk_D_1 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t74_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( v1_relat_1 @ D )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X14 ) )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t74_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_1 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','40'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
    | ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C )
   <= ( m1_subset_1 @ sk_F @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X27 @ sk_B ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('49',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C ) )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_C )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
          | ~ ( r2_hidden @ X27 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
    | ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_C )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_E ) @ sk_D_1 )
        | ~ ( r2_hidden @ X27 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('53',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('54',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('55',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ X6 @ ( k9_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('59',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('60',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('61',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('63',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','44','51','52','53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f6iu7Be9nN
% 0.15/0.37  % Computer   : n015.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 15:10:53 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.54  % Solved by: fo/fo7.sh
% 0.24/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.54  % done 127 iterations in 0.047s
% 0.24/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.54  % SZS output start Refutation
% 0.24/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.24/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.24/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.54  thf(t52_relset_1, conjecture,
% 0.24/0.54    (![A:$i]:
% 0.24/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.54       ( ![B:$i]:
% 0.24/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.24/0.54           ( ![C:$i]:
% 0.24/0.54             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.54               ( ![D:$i]:
% 0.24/0.54                 ( ( m1_subset_1 @
% 0.24/0.54                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.24/0.54                   ( ![E:$i]:
% 0.24/0.54                     ( ( m1_subset_1 @ E @ A ) =>
% 0.24/0.54                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.24/0.54                         ( ?[F:$i]:
% 0.24/0.54                           ( ( r2_hidden @ F @ B ) & 
% 0.24/0.54                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.24/0.54                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.54    (~( ![A:$i]:
% 0.24/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.54          ( ![B:$i]:
% 0.24/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.24/0.54              ( ![C:$i]:
% 0.24/0.54                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.24/0.54                  ( ![D:$i]:
% 0.24/0.54                    ( ( m1_subset_1 @
% 0.24/0.54                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.24/0.54                      ( ![E:$i]:
% 0.24/0.54                        ( ( m1_subset_1 @ E @ A ) =>
% 0.24/0.54                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.24/0.54                            ( ?[F:$i]:
% 0.24/0.54                              ( ( r2_hidden @ F @ B ) & 
% 0.24/0.54                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.24/0.54                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.54    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.24/0.54  thf('0', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)
% 0.24/0.54        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('1', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 0.24/0.54       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['0'])).
% 0.24/0.54  thf('2', plain,
% 0.24/0.54      (((m1_subset_1 @ sk_F @ sk_C)
% 0.24/0.54        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('3', plain,
% 0.24/0.54      (((m1_subset_1 @ sk_F @ sk_C)) | 
% 0.24/0.54       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['2'])).
% 0.24/0.54  thf('4', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.24/0.54  thf('5', plain,
% 0.24/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.24/0.54          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.24/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.24/0.54  thf('6', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0)
% 0.24/0.54           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.54  thf('7', plain,
% 0.24/0.54      (((r2_hidden @ sk_F @ sk_B)
% 0.24/0.54        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('8', plain,
% 0.24/0.54      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('split', [status(esa)], ['7'])).
% 0.24/0.54  thf('9', plain,
% 0.24/0.54      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['6', '8'])).
% 0.24/0.54  thf(t143_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ C ) =>
% 0.24/0.54       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.24/0.54         ( ?[D:$i]:
% 0.24/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.24/0.54             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.24/0.54             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.24/0.54  thf('10', plain,
% 0.24/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.24/0.54          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X5 @ X6) @ X6) @ X7)
% 0.24/0.54          | ~ (v1_relat_1 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.24/0.54  thf('11', plain,
% 0.24/0.54      (((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.54         | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_E) @ 
% 0.24/0.54            sk_D_1)))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.24/0.54  thf('12', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(cc1_relset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.54       ( v1_relat_1 @ C ) ))).
% 0.24/0.54  thf('13', plain,
% 0.24/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.54         ((v1_relat_1 @ X17)
% 0.24/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.24/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.54  thf('14', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('15', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_E) @ 
% 0.24/0.54         sk_D_1))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '14'])).
% 0.24/0.54  thf('16', plain,
% 0.24/0.54      (![X27 : $i]:
% 0.24/0.54         (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54          | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54          | ~ (r2_hidden @ X27 @ sk_B)
% 0.24/0.54          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf('17', plain,
% 0.24/0.54      ((![X27 : $i]:
% 0.24/0.54          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54           | ~ (r2_hidden @ X27 @ sk_B)))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))))),
% 0.24/0.54      inference('split', [status(esa)], ['16'])).
% 0.24/0.54  thf('18', plain,
% 0.24/0.54      (((~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)
% 0.24/0.54         | ~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C)))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.24/0.54             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.54  thf('19', plain,
% 0.24/0.54      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup+', [status(thm)], ['6', '8'])).
% 0.24/0.54  thf('20', plain,
% 0.24/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.24/0.54          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.24/0.54          | ~ (v1_relat_1 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.24/0.54  thf('21', plain,
% 0.24/0.54      (((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.54         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B)))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.54  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('23', plain,
% 0.24/0.54      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_B))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.24/0.54  thf('24', plain,
% 0.24/0.54      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.24/0.54             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('demod', [status(thm)], ['18', '23'])).
% 0.24/0.54  thf('25', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_E) @ 
% 0.24/0.54         sk_D_1))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('demod', [status(thm)], ['11', '14'])).
% 0.24/0.54  thf('26', plain,
% 0.24/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.24/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.54  thf(cc2_relset_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.54  thf('27', plain,
% 0.24/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.54         ((v4_relat_1 @ X20 @ X21)
% 0.24/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.24/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.54  thf('28', plain, ((v4_relat_1 @ sk_D_1 @ sk_C)),
% 0.24/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.54  thf(d18_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.54  thf('29', plain,
% 0.24/0.54      (![X2 : $i, X3 : $i]:
% 0.24/0.54         (~ (v4_relat_1 @ X2 @ X3)
% 0.24/0.54          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.24/0.54          | ~ (v1_relat_1 @ X2))),
% 0.24/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.24/0.54  thf('30', plain,
% 0.24/0.54      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_C))),
% 0.24/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.54  thf('31', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_C)),
% 0.24/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.24/0.54  thf(t77_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ B ) =>
% 0.24/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.24/0.54         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.24/0.54  thf('33', plain,
% 0.24/0.54      (![X15 : $i, X16 : $i]:
% 0.24/0.54         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.24/0.54          | ((k5_relat_1 @ (k6_relat_1 @ X16) @ X15) = (X15))
% 0.24/0.54          | ~ (v1_relat_1 @ X15))),
% 0.24/0.54      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.24/0.54  thf('34', plain,
% 0.24/0.54      ((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.54        | ((k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_D_1) = (sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.54  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('36', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_C) @ sk_D_1) = (sk_D_1))),
% 0.24/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.24/0.54  thf(t74_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ D ) =>
% 0.24/0.54       ( ( r2_hidden @
% 0.24/0.54           ( k4_tarski @ A @ B ) @ ( k5_relat_1 @ ( k6_relat_1 @ C ) @ D ) ) <=>
% 0.24/0.54         ( ( r2_hidden @ A @ C ) & ( r2_hidden @ ( k4_tarski @ A @ B ) @ D ) ) ) ))).
% 0.24/0.54  thf('37', plain,
% 0.24/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.54         (~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ 
% 0.24/0.54             (k5_relat_1 @ (k6_relat_1 @ X12) @ X14))
% 0.24/0.54          | (r2_hidden @ X11 @ X12)
% 0.24/0.54          | ~ (v1_relat_1 @ X14))),
% 0.24/0.54      inference('cnf', [status(esa)], [t74_relat_1])).
% 0.24/0.54  thf('38', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_1)
% 0.24/0.54          | ~ (v1_relat_1 @ sk_D_1)
% 0.24/0.54          | (r2_hidden @ X1 @ sk_C))),
% 0.24/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.24/0.54  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('40', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]:
% 0.24/0.54         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_D_1)
% 0.24/0.54          | (r2_hidden @ X1 @ sk_C))),
% 0.24/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.24/0.54  thf('41', plain,
% 0.24/0.54      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['25', '40'])).
% 0.24/0.54  thf(t1_subset, axiom,
% 0.24/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.24/0.54  thf('42', plain,
% 0.24/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.24/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.24/0.54  thf('43', plain,
% 0.24/0.54      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B @ sk_E) @ sk_C))
% 0.24/0.54         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.24/0.54  thf('44', plain,
% 0.24/0.54      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))) | 
% 0.24/0.54       ~
% 0.24/0.54       (![X27 : $i]:
% 0.24/0.54          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54           | ~ (r2_hidden @ X27 @ sk_B)))),
% 0.24/0.54      inference('demod', [status(thm)], ['24', '43'])).
% 0.24/0.54  thf('45', plain,
% 0.24/0.54      (((m1_subset_1 @ sk_F @ sk_C)) <= (((m1_subset_1 @ sk_F @ sk_C)))),
% 0.24/0.54      inference('split', [status(esa)], ['2'])).
% 0.24/0.54  thf('46', plain,
% 0.24/0.54      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['7'])).
% 0.24/0.54  thf('47', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('split', [status(esa)], ['0'])).
% 0.24/0.54  thf('48', plain,
% 0.24/0.54      ((![X27 : $i]:
% 0.24/0.54          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54           | ~ (r2_hidden @ X27 @ sk_B)))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))))),
% 0.24/0.54      inference('split', [status(esa)], ['16'])).
% 0.24/0.54  thf('49', plain,
% 0.24/0.54      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C)))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.24/0.54             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.24/0.54  thf('50', plain,
% 0.24/0.54      ((~ (m1_subset_1 @ sk_F @ sk_C))
% 0.24/0.54         <= ((![X27 : $i]:
% 0.24/0.54                (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54                 | ~ (r2_hidden @ X27 @ sk_B))) & 
% 0.24/0.54             ((r2_hidden @ sk_F @ sk_B)) & 
% 0.24/0.54             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['46', '49'])).
% 0.24/0.54  thf('51', plain,
% 0.24/0.54      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 0.24/0.54       ~
% 0.24/0.54       (![X27 : $i]:
% 0.24/0.54          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54           | ~ (r2_hidden @ X27 @ sk_B))) | 
% 0.24/0.54       ~ ((m1_subset_1 @ sk_F @ sk_C)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 0.24/0.54      inference('sup-', [status(thm)], ['45', '50'])).
% 0.24/0.54  thf('52', plain,
% 0.24/0.54      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))) | 
% 0.24/0.54       (![X27 : $i]:
% 0.24/0.54          (~ (m1_subset_1 @ X27 @ sk_C)
% 0.24/0.54           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_E) @ sk_D_1)
% 0.24/0.54           | ~ (r2_hidden @ X27 @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['16'])).
% 0.24/0.54  thf('53', plain,
% 0.24/0.54      (((r2_hidden @ sk_F @ sk_B)) | 
% 0.24/0.54       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['7'])).
% 0.24/0.54  thf('54', plain,
% 0.24/0.54      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 0.24/0.54      inference('split', [status(esa)], ['7'])).
% 0.24/0.54  thf('55', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('split', [status(esa)], ['0'])).
% 0.24/0.54  thf('56', plain,
% 0.24/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.24/0.54          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X7)
% 0.24/0.54          | ~ (r2_hidden @ X4 @ (k1_relat_1 @ X7))
% 0.24/0.54          | (r2_hidden @ X6 @ (k9_relat_1 @ X7 @ X5))
% 0.24/0.54          | ~ (v1_relat_1 @ X7))),
% 0.24/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.24/0.54  thf('57', plain,
% 0.24/0.54      ((![X0 : $i]:
% 0.24/0.54          (~ (v1_relat_1 @ sk_D_1)
% 0.24/0.54           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.24/0.54           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 0.24/0.54           | ~ (r2_hidden @ sk_F @ X0)))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.24/0.54  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('59', plain,
% 0.24/0.54      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('split', [status(esa)], ['0'])).
% 0.24/0.54  thf(t20_relat_1, axiom,
% 0.24/0.54    (![A:$i,B:$i,C:$i]:
% 0.24/0.54     ( ( v1_relat_1 @ C ) =>
% 0.24/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.24/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.24/0.54           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.24/0.54  thf('60', plain,
% 0.24/0.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.54         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.24/0.54          | (r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.24/0.54          | ~ (v1_relat_1 @ X10))),
% 0.24/0.54      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.24/0.54  thf('61', plain,
% 0.24/0.54      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.24/0.54  thf('62', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.54  thf('63', plain,
% 0.24/0.54      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1)))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('demod', [status(thm)], ['61', '62'])).
% 0.24/0.54  thf('64', plain,
% 0.24/0.54      ((![X0 : $i]:
% 0.24/0.54          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.24/0.54           | ~ (r2_hidden @ sk_F @ X0)))
% 0.24/0.54         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('demod', [status(thm)], ['57', '58', '63'])).
% 0.24/0.54  thf('65', plain,
% 0.24/0.54      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 0.24/0.54             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['54', '64'])).
% 0.24/0.54  thf('66', plain,
% 0.24/0.54      (![X0 : $i]:
% 0.24/0.54         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0)
% 0.24/0.54           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.24/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.54  thf('67', plain,
% 0.24/0.54      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (~
% 0.24/0.54             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('split', [status(esa)], ['16'])).
% 0.24/0.54  thf('68', plain,
% 0.24/0.54      ((~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B)))
% 0.24/0.54         <= (~
% 0.24/0.54             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B))))),
% 0.24/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.24/0.54  thf('69', plain,
% 0.24/0.54      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 0.24/0.54       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 0.24/0.54       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B)))),
% 0.24/0.54      inference('sup-', [status(thm)], ['65', '68'])).
% 0.24/0.54  thf('70', plain, ($false),
% 0.24/0.54      inference('sat_resolution*', [status(thm)],
% 0.24/0.54                ['1', '3', '44', '51', '52', '53', '69'])).
% 0.24/0.54  
% 0.24/0.54  % SZS output end Refutation
% 0.24/0.54  
% 0.24/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
