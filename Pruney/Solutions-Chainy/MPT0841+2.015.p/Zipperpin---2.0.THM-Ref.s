%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Js4wOkf12D

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:24 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 171 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  758 (2581 expanded)
%              Number of equality atoms :    7 (  20 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X25 @ X23 @ X24 ) @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('17',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('19',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X0 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( m1_subset_1 @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k9_relat_1 @ X25 @ X23 ) )
      | ( r2_hidden @ ( sk_D_1 @ X25 @ X23 @ X24 ) @ X23 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k9_relat_1 @ X14 @ X13 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ~ ( r2_hidden @ X19 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X18 ) @ X14 )
      | ( r2_hidden @ X18 @ ( k9_relat_1 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ sk_E_2 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X30 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','37','38','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Js4wOkf12D
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:14:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.22/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.22/1.41  % Solved by: fo/fo7.sh
% 1.22/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.41  % done 598 iterations in 0.951s
% 1.22/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.22/1.41  % SZS output start Refutation
% 1.22/1.41  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.22/1.41  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.22/1.41  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.22/1.41  thf(sk_F_type, type, sk_F: $i).
% 1.22/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.22/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.22/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.22/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.22/1.41  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.22/1.41  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.22/1.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.22/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.22/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.41  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.22/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.22/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.22/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.22/1.41  thf(t52_relset_1, conjecture,
% 1.22/1.41    (![A:$i]:
% 1.22/1.41     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.22/1.41       ( ![B:$i]:
% 1.22/1.41         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.22/1.41           ( ![C:$i]:
% 1.22/1.41             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.22/1.41               ( ![D:$i]:
% 1.22/1.41                 ( ( m1_subset_1 @
% 1.22/1.41                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.22/1.41                   ( ![E:$i]:
% 1.22/1.41                     ( ( m1_subset_1 @ E @ A ) =>
% 1.22/1.41                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.22/1.41                         ( ?[F:$i]:
% 1.22/1.41                           ( ( r2_hidden @ F @ B ) & 
% 1.22/1.41                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.22/1.41                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.22/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.41    (~( ![A:$i]:
% 1.22/1.41        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.22/1.41          ( ![B:$i]:
% 1.22/1.41            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.22/1.41              ( ![C:$i]:
% 1.22/1.41                ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.22/1.41                  ( ![D:$i]:
% 1.22/1.41                    ( ( m1_subset_1 @
% 1.22/1.41                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.22/1.41                      ( ![E:$i]:
% 1.22/1.41                        ( ( m1_subset_1 @ E @ A ) =>
% 1.22/1.41                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.22/1.41                            ( ?[F:$i]:
% 1.22/1.41                              ( ( r2_hidden @ F @ B ) & 
% 1.22/1.41                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.22/1.41                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.22/1.41    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 1.22/1.41  thf('0', plain,
% 1.22/1.41      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)
% 1.22/1.41        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('1', plain,
% 1.22/1.41      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 1.22/1.41       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('split', [status(esa)], ['0'])).
% 1.22/1.41  thf('2', plain,
% 1.22/1.41      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf(redefinition_k7_relset_1, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.22/1.41       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.22/1.41  thf('3', plain,
% 1.22/1.41      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.22/1.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.22/1.41          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 1.22/1.41      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.22/1.41  thf('4', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0)
% 1.22/1.41           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.22/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.22/1.41  thf('5', plain,
% 1.22/1.41      (((r2_hidden @ sk_F @ sk_B)
% 1.22/1.41        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('6', plain,
% 1.22/1.41      (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('split', [status(esa)], ['5'])).
% 1.22/1.41  thf('7', plain,
% 1.22/1.41      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['4', '6'])).
% 1.22/1.41  thf(t143_relat_1, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i]:
% 1.22/1.41     ( ( v1_relat_1 @ C ) =>
% 1.22/1.41       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.22/1.41         ( ?[D:$i]:
% 1.22/1.41           ( ( r2_hidden @ D @ B ) & 
% 1.22/1.41             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.22/1.41             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.22/1.41  thf('8', plain,
% 1.22/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X24 @ (k9_relat_1 @ X25 @ X23))
% 1.22/1.41          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X25 @ X23 @ X24) @ X24) @ X25)
% 1.22/1.41          | ~ (v1_relat_1 @ X25))),
% 1.22/1.41      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.22/1.41  thf('9', plain,
% 1.22/1.41      (((~ (v1_relat_1 @ sk_D_2)
% 1.22/1.41         | (r2_hidden @ 
% 1.22/1.41            (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['7', '8'])).
% 1.22/1.41  thf('10', plain,
% 1.22/1.41      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf(cc2_relat_1, axiom,
% 1.22/1.41    (![A:$i]:
% 1.22/1.41     ( ( v1_relat_1 @ A ) =>
% 1.22/1.41       ( ![B:$i]:
% 1.22/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.22/1.41  thf('11', plain,
% 1.22/1.41      (![X10 : $i, X11 : $i]:
% 1.22/1.41         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 1.22/1.41          | (v1_relat_1 @ X10)
% 1.22/1.41          | ~ (v1_relat_1 @ X11))),
% 1.22/1.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.22/1.41  thf('12', plain,
% 1.22/1.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_D_2))),
% 1.22/1.41      inference('sup-', [status(thm)], ['10', '11'])).
% 1.22/1.41  thf(fc6_relat_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.22/1.41  thf('13', plain,
% 1.22/1.41      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.22/1.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.22/1.41  thf('14', plain, ((v1_relat_1 @ sk_D_2)),
% 1.22/1.41      inference('demod', [status(thm)], ['12', '13'])).
% 1.22/1.41  thf('15', plain,
% 1.22/1.41      (((r2_hidden @ 
% 1.22/1.41         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('demod', [status(thm)], ['9', '14'])).
% 1.22/1.41  thf('16', plain,
% 1.22/1.41      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['4', '6'])).
% 1.22/1.41  thf('17', plain,
% 1.22/1.41      (![X30 : $i]:
% 1.22/1.41         (~ (m1_subset_1 @ X30 @ sk_C)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_E_2) @ sk_D_2)
% 1.22/1.41          | ~ (r2_hidden @ X30 @ sk_B)
% 1.22/1.41          | ~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('18', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0)
% 1.22/1.41           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.22/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.22/1.41  thf('19', plain,
% 1.22/1.41      (![X30 : $i]:
% 1.22/1.41         (~ (m1_subset_1 @ X30 @ sk_C)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_E_2) @ sk_D_2)
% 1.22/1.41          | ~ (r2_hidden @ X30 @ sk_B)
% 1.22/1.41          | ~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('demod', [status(thm)], ['17', '18'])).
% 1.22/1.41  thf('20', plain,
% 1.22/1.41      ((![X0 : $i]:
% 1.22/1.41          (~ (r2_hidden @ X0 @ sk_B)
% 1.22/1.41           | ~ (r2_hidden @ (k4_tarski @ X0 @ sk_E_2) @ sk_D_2)
% 1.22/1.41           | ~ (m1_subset_1 @ X0 @ sk_C)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['16', '19'])).
% 1.22/1.41  thf('21', plain,
% 1.22/1.41      (((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C)
% 1.22/1.41         | ~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['15', '20'])).
% 1.22/1.41  thf('22', plain,
% 1.22/1.41      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup+', [status(thm)], ['4', '6'])).
% 1.22/1.41  thf('23', plain,
% 1.22/1.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X24 @ (k9_relat_1 @ X25 @ X23))
% 1.22/1.41          | (r2_hidden @ (sk_D_1 @ X25 @ X23 @ X24) @ X23)
% 1.22/1.41          | ~ (v1_relat_1 @ X25))),
% 1.22/1.41      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.22/1.41  thf('24', plain,
% 1.22/1.41      (((~ (v1_relat_1 @ sk_D_2)
% 1.22/1.41         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['22', '23'])).
% 1.22/1.41  thf('25', plain, ((v1_relat_1 @ sk_D_2)),
% 1.22/1.41      inference('demod', [status(thm)], ['12', '13'])).
% 1.22/1.41  thf('26', plain,
% 1.22/1.41      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('demod', [status(thm)], ['24', '25'])).
% 1.22/1.41  thf('27', plain,
% 1.22/1.41      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('demod', [status(thm)], ['21', '26'])).
% 1.22/1.41  thf('28', plain,
% 1.22/1.41      (((r2_hidden @ 
% 1.22/1.41         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('demod', [status(thm)], ['9', '14'])).
% 1.22/1.41  thf('29', plain,
% 1.22/1.41      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf(l3_subset_1, axiom,
% 1.22/1.41    (![A:$i,B:$i]:
% 1.22/1.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.41       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.22/1.41  thf('30', plain,
% 1.22/1.41      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.41         (~ (r2_hidden @ X5 @ X6)
% 1.22/1.41          | (r2_hidden @ X5 @ X7)
% 1.22/1.41          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.22/1.41      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.22/1.41  thf('31', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_A))
% 1.22/1.41          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 1.22/1.41      inference('sup-', [status(thm)], ['29', '30'])).
% 1.22/1.41  thf('32', plain,
% 1.22/1.41      (((r2_hidden @ 
% 1.22/1.41         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ 
% 1.22/1.41         (k2_zfmisc_1 @ sk_C @ sk_A)))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['28', '31'])).
% 1.22/1.41  thf(l54_zfmisc_1, axiom,
% 1.22/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.41     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.22/1.41       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.22/1.41  thf('33', plain,
% 1.22/1.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.41         ((r2_hidden @ X0 @ X1)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 1.22/1.41      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.22/1.41  thf('34', plain,
% 1.22/1.41      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['32', '33'])).
% 1.22/1.41  thf(t1_subset, axiom,
% 1.22/1.41    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.22/1.41  thf('35', plain,
% 1.22/1.41      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 1.22/1.41      inference('cnf', [status(esa)], [t1_subset])).
% 1.22/1.41  thf('36', plain,
% 1.22/1.41      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C))
% 1.22/1.41         <= (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['34', '35'])).
% 1.22/1.41  thf('37', plain,
% 1.22/1.41      (~ ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('demod', [status(thm)], ['27', '36'])).
% 1.22/1.41  thf('38', plain,
% 1.22/1.41      (((r2_hidden @ sk_F @ sk_B)) | 
% 1.22/1.41       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('split', [status(esa)], ['5'])).
% 1.22/1.41  thf('39', plain,
% 1.22/1.41      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 1.22/1.41      inference('split', [status(esa)], ['5'])).
% 1.22/1.41  thf('40', plain,
% 1.22/1.41      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2))
% 1.22/1.41         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.22/1.41      inference('split', [status(esa)], ['0'])).
% 1.22/1.41  thf(d13_relat_1, axiom,
% 1.22/1.41    (![A:$i]:
% 1.22/1.41     ( ( v1_relat_1 @ A ) =>
% 1.22/1.41       ( ![B:$i,C:$i]:
% 1.22/1.41         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.22/1.41           ( ![D:$i]:
% 1.22/1.41             ( ( r2_hidden @ D @ C ) <=>
% 1.22/1.41               ( ?[E:$i]:
% 1.22/1.41                 ( ( r2_hidden @ E @ B ) & 
% 1.22/1.41                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 1.22/1.41  thf('41', plain,
% 1.22/1.41      (![X13 : $i, X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 1.22/1.41         (((X16) != (k9_relat_1 @ X14 @ X13))
% 1.22/1.41          | (r2_hidden @ X18 @ X16)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 1.22/1.41          | ~ (r2_hidden @ X19 @ X13)
% 1.22/1.41          | ~ (v1_relat_1 @ X14))),
% 1.22/1.41      inference('cnf', [status(esa)], [d13_relat_1])).
% 1.22/1.41  thf('42', plain,
% 1.22/1.41      (![X13 : $i, X14 : $i, X18 : $i, X19 : $i]:
% 1.22/1.41         (~ (v1_relat_1 @ X14)
% 1.22/1.41          | ~ (r2_hidden @ X19 @ X13)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X19 @ X18) @ X14)
% 1.22/1.41          | (r2_hidden @ X18 @ (k9_relat_1 @ X14 @ X13)))),
% 1.22/1.41      inference('simplify', [status(thm)], ['41'])).
% 1.22/1.41  thf('43', plain,
% 1.22/1.41      ((![X0 : $i]:
% 1.22/1.41          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 1.22/1.41           | ~ (r2_hidden @ sk_F @ X0)
% 1.22/1.41           | ~ (v1_relat_1 @ sk_D_2)))
% 1.22/1.41         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['40', '42'])).
% 1.22/1.41  thf('44', plain, ((v1_relat_1 @ sk_D_2)),
% 1.22/1.41      inference('demod', [status(thm)], ['12', '13'])).
% 1.22/1.41  thf('45', plain,
% 1.22/1.41      ((![X0 : $i]:
% 1.22/1.41          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 1.22/1.41           | ~ (r2_hidden @ sk_F @ X0)))
% 1.22/1.41         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.22/1.41      inference('demod', [status(thm)], ['43', '44'])).
% 1.22/1.41  thf('46', plain,
% 1.22/1.41      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 1.22/1.41             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.22/1.41      inference('sup-', [status(thm)], ['39', '45'])).
% 1.22/1.41  thf('47', plain,
% 1.22/1.41      (![X0 : $i]:
% 1.22/1.41         ((k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ X0)
% 1.22/1.41           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.22/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.22/1.41  thf('48', plain,
% 1.22/1.41      (![X30 : $i]:
% 1.22/1.41         (~ (m1_subset_1 @ X30 @ sk_C)
% 1.22/1.41          | ~ (r2_hidden @ (k4_tarski @ X30 @ sk_E_2) @ sk_D_2)
% 1.22/1.41          | ~ (r2_hidden @ X30 @ sk_B)
% 1.22/1.41          | ~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))),
% 1.22/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.41  thf('49', plain,
% 1.22/1.41      ((~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (~
% 1.22/1.41             ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('split', [status(esa)], ['48'])).
% 1.22/1.41  thf('50', plain,
% 1.22/1.41      ((~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.22/1.41         <= (~
% 1.22/1.41             ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))))),
% 1.22/1.41      inference('sup-', [status(thm)], ['47', '49'])).
% 1.22/1.41  thf('51', plain,
% 1.22/1.41      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 1.22/1.41       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C @ sk_A @ sk_D_2 @ sk_B))) | 
% 1.22/1.41       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2))),
% 1.22/1.41      inference('sup-', [status(thm)], ['46', '50'])).
% 1.22/1.41  thf('52', plain, ($false),
% 1.22/1.41      inference('sat_resolution*', [status(thm)], ['1', '37', '38', '51'])).
% 1.22/1.41  
% 1.22/1.41  % SZS output end Refutation
% 1.22/1.41  
% 1.22/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
