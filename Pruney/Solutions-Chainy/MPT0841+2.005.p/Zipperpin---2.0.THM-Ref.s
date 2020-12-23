%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXsWW8ZU9C

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:22 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 174 expanded)
%              Number of leaves         :   26 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  791 (2757 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ( r2_hidden @ sk_F @ sk_B_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_1 )
      | ~ ( r2_hidden @ X29 @ sk_B_1 )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_1 )
      | ~ ( r2_hidden @ X29 @ sk_B_1 )
      | ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_E ) @ sk_D_1 )
        | ~ ( m1_subset_1 @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('21',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_B_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_E ) @ sk_C )
   <= ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_F @ sk_B_1 )
   <= ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_D_1 )
        | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(split,[status(esa)],['35'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,
    ( ( r2_hidden @ sk_F @ ( k1_relat_1 @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_F @ sk_B_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X29 @ sk_E ) @ sk_D_1 )
      | ~ ( r2_hidden @ X29 @ sk_B_1 )
      | ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E ) @ sk_D_1 )
    | ( r2_hidden @ sk_E @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','34','36','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXsWW8ZU9C
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:15:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.90/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.10  % Solved by: fo/fo7.sh
% 0.90/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.10  % done 879 iterations in 0.655s
% 0.90/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.10  % SZS output start Refutation
% 0.90/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.10  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.90/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.10  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.90/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.10  thf(sk_F_type, type, sk_F: $i).
% 0.90/1.10  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.10  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.90/1.10  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.90/1.10  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.90/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.10  thf(t52_relset_1, conjecture,
% 0.90/1.10    (![A:$i]:
% 0.90/1.10     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.10       ( ![B:$i]:
% 0.90/1.10         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.10           ( ![C:$i]:
% 0.90/1.10             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.10               ( ![D:$i]:
% 0.90/1.10                 ( ( m1_subset_1 @
% 0.90/1.10                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.90/1.10                   ( ![E:$i]:
% 0.90/1.10                     ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.10                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.90/1.10                         ( ?[F:$i]:
% 0.90/1.10                           ( ( r2_hidden @ F @ B ) & 
% 0.90/1.10                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.90/1.10                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.10    (~( ![A:$i]:
% 0.90/1.10        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.10          ( ![B:$i]:
% 0.90/1.10            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.90/1.10              ( ![C:$i]:
% 0.90/1.10                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.90/1.10                  ( ![D:$i]:
% 0.90/1.10                    ( ( m1_subset_1 @
% 0.90/1.10                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.90/1.10                      ( ![E:$i]:
% 0.90/1.10                        ( ( m1_subset_1 @ E @ A ) =>
% 0.90/1.10                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.90/1.10                            ( ?[F:$i]:
% 0.90/1.10                              ( ( r2_hidden @ F @ B ) & 
% 0.90/1.10                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.90/1.10                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.90/1.10    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 0.90/1.10  thf('0', plain,
% 0.90/1.10      (((r2_hidden @ sk_F @ sk_B_1)
% 0.90/1.10        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('1', plain,
% 0.90/1.10      (((r2_hidden @ sk_F @ sk_B_1)) | 
% 0.90/1.10       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('2', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(redefinition_k7_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.90/1.10  thf('3', plain,
% 0.90/1.10      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.90/1.10          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.90/1.10      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.90/1.10  thf('4', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0)
% 0.90/1.10           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('5', plain,
% 0.90/1.10      (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('6', plain,
% 0.90/1.10      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf(t143_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.90/1.10         ( ?[D:$i]:
% 0.90/1.10           ( ( r2_hidden @ D @ B ) & 
% 0.90/1.10             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.90/1.10             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.90/1.10  thf('7', plain,
% 0.90/1.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.90/1.10          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.90/1.10          | ~ (v1_relat_1 @ X18))),
% 0.90/1.10      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.90/1.10  thf('8', plain,
% 0.90/1.10      (((~ (v1_relat_1 @ sk_D_1)
% 0.90/1.10         | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 0.90/1.10            sk_D_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.90/1.10  thf('9', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(cc1_relset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.10       ( v1_relat_1 @ C ) ))).
% 0.90/1.10  thf('10', plain,
% 0.90/1.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.90/1.10         ((v1_relat_1 @ X22)
% 0.90/1.10          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.90/1.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.10  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.10  thf('12', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 0.90/1.10         sk_D_1))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('demod', [status(thm)], ['8', '11'])).
% 0.90/1.10  thf('13', plain,
% 0.90/1.10      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf('14', plain,
% 0.90/1.10      (![X29 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X29 @ sk_C)
% 0.90/1.10          | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_1)
% 0.90/1.10          | ~ (r2_hidden @ X29 @ sk_B_1)
% 0.90/1.10          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('15', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0)
% 0.90/1.10           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('16', plain,
% 0.90/1.10      (![X29 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X29 @ sk_C)
% 0.90/1.10          | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_1)
% 0.90/1.10          | ~ (r2_hidden @ X29 @ sk_B_1)
% 0.90/1.10          | ~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.90/1.10  thf('17', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.90/1.10           | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_E) @ sk_D_1)
% 0.90/1.10           | ~ (m1_subset_1 @ X0 @ sk_C)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['13', '16'])).
% 0.90/1.10  thf('18', plain,
% 0.90/1.10      (((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C)
% 0.90/1.10         | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['12', '17'])).
% 0.90/1.10  thf('19', plain,
% 0.90/1.10      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup+', [status(thm)], ['4', '5'])).
% 0.90/1.10  thf('20', plain,
% 0.90/1.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.90/1.10          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.90/1.10          | ~ (v1_relat_1 @ X18))),
% 0.90/1.10      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.90/1.10  thf('21', plain,
% 0.90/1.10      (((~ (v1_relat_1 @ sk_D_1)
% 0.90/1.10         | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.10  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.10  thf('23', plain,
% 0.90/1.10      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_B_1))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.10  thf('24', plain,
% 0.90/1.10      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('demod', [status(thm)], ['18', '23'])).
% 0.90/1.10  thf('25', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 0.90/1.10         sk_D_1))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('demod', [status(thm)], ['8', '11'])).
% 0.90/1.10  thf('26', plain,
% 0.90/1.10      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf(l3_subset_1, axiom,
% 0.90/1.10    (![A:$i,B:$i]:
% 0.90/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.10       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.90/1.10  thf('27', plain,
% 0.90/1.10      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X8 @ X9)
% 0.90/1.10          | (r2_hidden @ X8 @ X10)
% 0.90/1.10          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.90/1.10      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.90/1.10  thf('28', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 0.90/1.10          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.10  thf('29', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_E) @ 
% 0.90/1.10         (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['25', '28'])).
% 0.90/1.10  thf(l54_zfmisc_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.10     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.90/1.10       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.90/1.10  thf('30', plain,
% 0.90/1.10      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.90/1.10         ((r2_hidden @ X3 @ X4)
% 0.90/1.10          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.90/1.10      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.90/1.10  thf('31', plain,
% 0.90/1.10      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.10  thf(t1_subset, axiom,
% 0.90/1.10    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.10  thf('32', plain,
% 0.90/1.10      (![X11 : $i, X12 : $i]:
% 0.90/1.10         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.90/1.10      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.10  thf('33', plain,
% 0.90/1.10      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_E) @ sk_C))
% 0.90/1.10         <= (((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.10  thf('34', plain,
% 0.90/1.10      (~ ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['24', '33'])).
% 0.90/1.10  thf('35', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)
% 0.90/1.10        | (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('36', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 0.90/1.10       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['35'])).
% 0.90/1.10  thf('37', plain,
% 0.90/1.10      (((r2_hidden @ sk_F @ sk_B_1)) <= (((r2_hidden @ sk_F @ sk_B_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['0'])).
% 0.90/1.10  thf('38', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['35'])).
% 0.90/1.10  thf('39', plain,
% 0.90/1.10      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.90/1.10         (~ (r2_hidden @ X15 @ X16)
% 0.90/1.10          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X18)
% 0.90/1.10          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.90/1.10          | (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.90/1.10          | ~ (v1_relat_1 @ X18))),
% 0.90/1.10      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.90/1.10  thf('40', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          (~ (v1_relat_1 @ sk_D_1)
% 0.90/1.10           | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.90/1.10           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 0.90/1.10           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['38', '39'])).
% 0.90/1.10  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.10  thf('42', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.90/1.10           | ~ (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))
% 0.90/1.10           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['40', '41'])).
% 0.90/1.10  thf('43', plain,
% 0.90/1.10      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('split', [status(esa)], ['35'])).
% 0.90/1.10  thf(t20_relat_1, axiom,
% 0.90/1.10    (![A:$i,B:$i,C:$i]:
% 0.90/1.10     ( ( v1_relat_1 @ C ) =>
% 0.90/1.10       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.90/1.10         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.90/1.10           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.90/1.10  thf('44', plain,
% 0.90/1.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.10         (~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21)
% 0.90/1.10          | (r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 0.90/1.10          | ~ (v1_relat_1 @ X21))),
% 0.90/1.10      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.90/1.10  thf('45', plain,
% 0.90/1.10      (((~ (v1_relat_1 @ sk_D_1) | (r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1))))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.10  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.90/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.10  thf('47', plain,
% 0.90/1.10      (((r2_hidden @ sk_F @ (k1_relat_1 @ sk_D_1)))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['45', '46'])).
% 0.90/1.10  thf('48', plain,
% 0.90/1.10      ((![X0 : $i]:
% 0.90/1.10          ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.90/1.10           | ~ (r2_hidden @ sk_F @ X0)))
% 0.90/1.10         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('demod', [status(thm)], ['42', '47'])).
% 0.90/1.10  thf('49', plain,
% 0.90/1.10      (((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (((r2_hidden @ sk_F @ sk_B_1)) & 
% 0.90/1.10             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)))),
% 0.90/1.10      inference('sup-', [status(thm)], ['37', '48'])).
% 0.90/1.10  thf('50', plain,
% 0.90/1.10      (![X0 : $i]:
% 0.90/1.10         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ X0)
% 0.90/1.10           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.90/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.10  thf('51', plain,
% 0.90/1.10      (![X29 : $i]:
% 0.90/1.10         (~ (m1_subset_1 @ X29 @ sk_C)
% 0.90/1.10          | ~ (r2_hidden @ (k4_tarski @ X29 @ sk_E) @ sk_D_1)
% 0.90/1.10          | ~ (r2_hidden @ X29 @ sk_B_1)
% 0.90/1.10          | ~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))),
% 0.90/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.10  thf('52', plain,
% 0.90/1.10      ((~ (r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (~
% 0.90/1.10             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('split', [status(esa)], ['51'])).
% 0.90/1.10  thf('53', plain,
% 0.90/1.10      ((~ (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_B_1)))
% 0.90/1.10         <= (~
% 0.90/1.10             ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))))),
% 0.90/1.10      inference('sup-', [status(thm)], ['50', '52'])).
% 0.90/1.10  thf('54', plain,
% 0.90/1.10      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E) @ sk_D_1)) | 
% 0.90/1.10       ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_1 @ sk_B_1))) | 
% 0.90/1.10       ~ ((r2_hidden @ sk_F @ sk_B_1))),
% 0.90/1.10      inference('sup-', [status(thm)], ['49', '53'])).
% 0.90/1.10  thf('55', plain, ($false),
% 0.90/1.10      inference('sat_resolution*', [status(thm)], ['1', '34', '36', '54'])).
% 0.90/1.10  
% 0.90/1.10  % SZS output end Refutation
% 0.90/1.10  
% 0.90/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
