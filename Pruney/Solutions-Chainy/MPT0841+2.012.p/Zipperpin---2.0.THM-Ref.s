%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gOza5OWYT

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:23 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 184 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  905 (2907 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k7_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k9_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k9_relat_1 @ X29 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X29 @ X27 @ X28 ) @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ ( k2_zfmisc_1 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('29',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X34 @ sk_B )
      | ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X34 @ sk_B ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','8'])).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k9_relat_1 @ X29 @ X27 ) )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X27 @ X28 ) @ X27 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,
    ( ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_B )
   <= ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2 ) @ sk_C_1 )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) )
      & ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( m1_subset_1 @ sk_F @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X34 @ sk_B ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('43',plain,
    ( ( ~ ( r2_hidden @ sk_F @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ sk_C_1 ) )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) )
      & ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
          | ~ ( r2_hidden @ X34 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ sk_C_1 )
    | ~ ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
    | ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_E_2 ) @ sk_D_2 )
        | ~ ( r2_hidden @ X34 @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('47',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('48',plain,
    ( ( r2_hidden @ sk_F @ sk_B )
   <= ( r2_hidden @ sk_F @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('49',plain,
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

thf('50',plain,(
    ! [X17: $i,X18: $i,X20: $i,X22: $i,X23: $i] :
      ( ( X20
       != ( k9_relat_1 @ X18 @ X17 ) )
      | ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X18 )
      | ~ ( r2_hidden @ X23 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('51',plain,(
    ! [X17: $i,X18: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( r2_hidden @ X23 @ X17 )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X22 ) @ X18 )
      | ( r2_hidden @ X22 @ ( k9_relat_1 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 )
        | ~ ( v1_relat_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ X0 ) )
        | ~ ( r2_hidden @ sk_F @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ( ( r2_hidden @ sk_F @ sk_B )
      & ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_F @ sk_B )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_F @ sk_E_2 ) @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','38','45','46','47','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gOza5OWYT
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:28:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 1.21/1.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.42  % Solved by: fo/fo7.sh
% 1.21/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.42  % done 749 iterations in 0.982s
% 1.21/1.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.42  % SZS output start Refutation
% 1.21/1.42  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.21/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.42  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.21/1.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.21/1.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.21/1.42  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.21/1.42  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.21/1.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.21/1.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.42  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.21/1.42  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.21/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.42  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.21/1.42  thf(sk_F_type, type, sk_F: $i).
% 1.21/1.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.21/1.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.42  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.42  thf(t52_relset_1, conjecture,
% 1.21/1.42    (![A:$i]:
% 1.21/1.42     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.21/1.42       ( ![B:$i]:
% 1.21/1.42         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.42           ( ![C:$i]:
% 1.21/1.42             ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.21/1.42               ( ![D:$i]:
% 1.21/1.42                 ( ( m1_subset_1 @
% 1.21/1.42                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.21/1.42                   ( ![E:$i]:
% 1.21/1.42                     ( ( m1_subset_1 @ E @ A ) =>
% 1.21/1.42                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.21/1.42                         ( ?[F:$i]:
% 1.21/1.42                           ( ( r2_hidden @ F @ B ) & 
% 1.21/1.42                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.21/1.42                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.21/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.42    (~( ![A:$i]:
% 1.21/1.42        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.21/1.42          ( ![B:$i]:
% 1.21/1.42            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.21/1.42              ( ![C:$i]:
% 1.21/1.42                ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.21/1.42                  ( ![D:$i]:
% 1.21/1.42                    ( ( m1_subset_1 @
% 1.21/1.42                        D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 1.21/1.42                      ( ![E:$i]:
% 1.21/1.42                        ( ( m1_subset_1 @ E @ A ) =>
% 1.21/1.42                          ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 1.21/1.42                            ( ?[F:$i]:
% 1.21/1.42                              ( ( r2_hidden @ F @ B ) & 
% 1.21/1.42                                ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 1.21/1.42                                ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.21/1.42    inference('cnf.neg', [status(esa)], [t52_relset_1])).
% 1.21/1.42  thf('0', plain,
% 1.21/1.42      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)
% 1.21/1.42        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('1', plain,
% 1.21/1.42      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 1.21/1.42       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['0'])).
% 1.21/1.42  thf('2', plain,
% 1.21/1.42      (((m1_subset_1 @ sk_F @ sk_C_1)
% 1.21/1.42        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('3', plain,
% 1.21/1.42      (((m1_subset_1 @ sk_F @ sk_C_1)) | 
% 1.21/1.42       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['2'])).
% 1.21/1.42  thf('4', plain,
% 1.21/1.42      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf(redefinition_k7_relset_1, axiom,
% 1.21/1.42    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.21/1.42       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.21/1.42  thf('5', plain,
% 1.21/1.42      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.21/1.42         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.21/1.42          | ((k7_relset_1 @ X31 @ X32 @ X30 @ X33) = (k9_relat_1 @ X30 @ X33)))),
% 1.21/1.42      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.21/1.42  thf('6', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0)
% 1.21/1.42           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.21/1.42      inference('sup-', [status(thm)], ['4', '5'])).
% 1.21/1.42  thf('7', plain,
% 1.21/1.42      (((r2_hidden @ sk_F @ sk_B)
% 1.21/1.42        | (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('8', plain,
% 1.21/1.42      (((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('split', [status(esa)], ['7'])).
% 1.21/1.42  thf('9', plain,
% 1.21/1.42      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup+', [status(thm)], ['6', '8'])).
% 1.21/1.42  thf(t143_relat_1, axiom,
% 1.21/1.42    (![A:$i,B:$i,C:$i]:
% 1.21/1.42     ( ( v1_relat_1 @ C ) =>
% 1.21/1.42       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.21/1.42         ( ?[D:$i]:
% 1.21/1.42           ( ( r2_hidden @ D @ B ) & 
% 1.21/1.42             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.21/1.42             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.21/1.42  thf('10', plain,
% 1.21/1.42      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.21/1.42         (~ (r2_hidden @ X28 @ (k9_relat_1 @ X29 @ X27))
% 1.21/1.42          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X29 @ X27 @ X28) @ X28) @ X29)
% 1.21/1.42          | ~ (v1_relat_1 @ X29))),
% 1.21/1.42      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.21/1.42  thf('11', plain,
% 1.21/1.42      (((~ (v1_relat_1 @ sk_D_2)
% 1.21/1.42         | (r2_hidden @ 
% 1.21/1.42            (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['9', '10'])).
% 1.21/1.42  thf('12', plain,
% 1.21/1.42      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf(cc2_relat_1, axiom,
% 1.21/1.42    (![A:$i]:
% 1.21/1.42     ( ( v1_relat_1 @ A ) =>
% 1.21/1.42       ( ![B:$i]:
% 1.21/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.21/1.42  thf('13', plain,
% 1.21/1.42      (![X14 : $i, X15 : $i]:
% 1.21/1.42         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.21/1.42          | (v1_relat_1 @ X14)
% 1.21/1.42          | ~ (v1_relat_1 @ X15))),
% 1.21/1.42      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.21/1.42  thf('14', plain,
% 1.21/1.42      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_D_2))),
% 1.21/1.42      inference('sup-', [status(thm)], ['12', '13'])).
% 1.21/1.42  thf(fc6_relat_1, axiom,
% 1.21/1.42    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.21/1.42  thf('15', plain,
% 1.21/1.42      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.21/1.42      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.21/1.42  thf('16', plain, ((v1_relat_1 @ sk_D_2)),
% 1.21/1.42      inference('demod', [status(thm)], ['14', '15'])).
% 1.21/1.42  thf('17', plain,
% 1.21/1.42      (((r2_hidden @ 
% 1.21/1.42         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('demod', [status(thm)], ['11', '16'])).
% 1.21/1.42  thf('18', plain,
% 1.21/1.42      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf(t3_subset, axiom,
% 1.21/1.42    (![A:$i,B:$i]:
% 1.21/1.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.21/1.42  thf('19', plain,
% 1.21/1.42      (![X11 : $i, X12 : $i]:
% 1.21/1.42         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.21/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.42  thf('20', plain, ((r1_tarski @ sk_D_2 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))),
% 1.21/1.42      inference('sup-', [status(thm)], ['18', '19'])).
% 1.21/1.42  thf(d3_tarski, axiom,
% 1.21/1.42    (![A:$i,B:$i]:
% 1.21/1.42     ( ( r1_tarski @ A @ B ) <=>
% 1.21/1.42       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.21/1.42  thf('21', plain,
% 1.21/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.21/1.42         (~ (r2_hidden @ X0 @ X1)
% 1.21/1.42          | (r2_hidden @ X0 @ X2)
% 1.21/1.42          | ~ (r1_tarski @ X1 @ X2))),
% 1.21/1.42      inference('cnf', [status(esa)], [d3_tarski])).
% 1.21/1.42  thf('22', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A))
% 1.21/1.42          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 1.21/1.42      inference('sup-', [status(thm)], ['20', '21'])).
% 1.21/1.42  thf('23', plain,
% 1.21/1.42      (((r2_hidden @ 
% 1.21/1.42         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ 
% 1.21/1.42         (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['17', '22'])).
% 1.21/1.42  thf(l54_zfmisc_1, axiom,
% 1.21/1.42    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.42     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.21/1.42       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.21/1.42  thf('24', plain,
% 1.21/1.42      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.21/1.42         ((r2_hidden @ X4 @ X5)
% 1.21/1.42          | ~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ (k2_zfmisc_1 @ X5 @ X7)))),
% 1.21/1.42      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.21/1.42  thf('25', plain,
% 1.21/1.42      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['23', '24'])).
% 1.21/1.42  thf(t1_subset, axiom,
% 1.21/1.42    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.21/1.42  thf('26', plain,
% 1.21/1.42      (![X9 : $i, X10 : $i]:
% 1.21/1.42         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 1.21/1.42      inference('cnf', [status(esa)], [t1_subset])).
% 1.21/1.42  thf('27', plain,
% 1.21/1.42      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['25', '26'])).
% 1.21/1.42  thf('28', plain,
% 1.21/1.42      (((r2_hidden @ 
% 1.21/1.42         (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_E_2) @ sk_D_2))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('demod', [status(thm)], ['11', '16'])).
% 1.21/1.42  thf('29', plain,
% 1.21/1.42      (![X34 : $i]:
% 1.21/1.42         (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42          | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42          | ~ (r2_hidden @ X34 @ sk_B)
% 1.21/1.42          | ~ (r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('30', plain,
% 1.21/1.42      ((![X34 : $i]:
% 1.21/1.42          (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42           | ~ (r2_hidden @ X34 @ sk_B)))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))))),
% 1.21/1.42      inference('split', [status(esa)], ['29'])).
% 1.21/1.42  thf('31', plain,
% 1.21/1.42      (((~ (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)
% 1.21/1.42         | ~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1)))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))) & 
% 1.21/1.42             ((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['28', '30'])).
% 1.21/1.42  thf('32', plain,
% 1.21/1.42      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup+', [status(thm)], ['6', '8'])).
% 1.21/1.42  thf('33', plain,
% 1.21/1.42      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.21/1.42         (~ (r2_hidden @ X28 @ (k9_relat_1 @ X29 @ X27))
% 1.21/1.42          | (r2_hidden @ (sk_D_1 @ X29 @ X27 @ X28) @ X27)
% 1.21/1.42          | ~ (v1_relat_1 @ X29))),
% 1.21/1.42      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.21/1.42  thf('34', plain,
% 1.21/1.42      (((~ (v1_relat_1 @ sk_D_2)
% 1.21/1.42         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B)))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['32', '33'])).
% 1.21/1.42  thf('35', plain, ((v1_relat_1 @ sk_D_2)),
% 1.21/1.42      inference('demod', [status(thm)], ['14', '15'])).
% 1.21/1.42  thf('36', plain,
% 1.21/1.42      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_B))
% 1.21/1.42         <= (((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('demod', [status(thm)], ['34', '35'])).
% 1.21/1.42  thf('37', plain,
% 1.21/1.42      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_B @ sk_E_2) @ sk_C_1))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))) & 
% 1.21/1.42             ((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('demod', [status(thm)], ['31', '36'])).
% 1.21/1.42  thf('38', plain,
% 1.21/1.42      (~ ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))) | 
% 1.21/1.42       ~
% 1.21/1.42       (![X34 : $i]:
% 1.21/1.42          (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42           | ~ (r2_hidden @ X34 @ sk_B)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['27', '37'])).
% 1.21/1.42  thf('39', plain,
% 1.21/1.42      (((m1_subset_1 @ sk_F @ sk_C_1)) <= (((m1_subset_1 @ sk_F @ sk_C_1)))),
% 1.21/1.42      inference('split', [status(esa)], ['2'])).
% 1.21/1.42  thf('40', plain,
% 1.21/1.42      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['7'])).
% 1.21/1.42  thf('41', plain,
% 1.21/1.42      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2))
% 1.21/1.42         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('split', [status(esa)], ['0'])).
% 1.21/1.42  thf('42', plain,
% 1.21/1.42      ((![X34 : $i]:
% 1.21/1.42          (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42           | ~ (r2_hidden @ X34 @ sk_B)))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))))),
% 1.21/1.42      inference('split', [status(esa)], ['29'])).
% 1.21/1.42  thf('43', plain,
% 1.21/1.42      (((~ (r2_hidden @ sk_F @ sk_B) | ~ (m1_subset_1 @ sk_F @ sk_C_1)))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))) & 
% 1.21/1.42             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['41', '42'])).
% 1.21/1.42  thf('44', plain,
% 1.21/1.42      ((~ (m1_subset_1 @ sk_F @ sk_C_1))
% 1.21/1.42         <= ((![X34 : $i]:
% 1.21/1.42                (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42                 | ~ (r2_hidden @ X34 @ sk_B))) & 
% 1.21/1.42             ((r2_hidden @ sk_F @ sk_B)) & 
% 1.21/1.42             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['40', '43'])).
% 1.21/1.42  thf('45', plain,
% 1.21/1.42      (~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 1.21/1.42       ~
% 1.21/1.42       (![X34 : $i]:
% 1.21/1.42          (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42           | ~ (r2_hidden @ X34 @ sk_B))) | 
% 1.21/1.42       ~ ((m1_subset_1 @ sk_F @ sk_C_1)) | ~ ((r2_hidden @ sk_F @ sk_B))),
% 1.21/1.42      inference('sup-', [status(thm)], ['39', '44'])).
% 1.21/1.42  thf('46', plain,
% 1.21/1.42      (~ ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))) | 
% 1.21/1.42       (![X34 : $i]:
% 1.21/1.42          (~ (m1_subset_1 @ X34 @ sk_C_1)
% 1.21/1.42           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_E_2) @ sk_D_2)
% 1.21/1.42           | ~ (r2_hidden @ X34 @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['29'])).
% 1.21/1.42  thf('47', plain,
% 1.21/1.42      (((r2_hidden @ sk_F @ sk_B)) | 
% 1.21/1.42       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['7'])).
% 1.21/1.42  thf('48', plain,
% 1.21/1.42      (((r2_hidden @ sk_F @ sk_B)) <= (((r2_hidden @ sk_F @ sk_B)))),
% 1.21/1.42      inference('split', [status(esa)], ['7'])).
% 1.21/1.42  thf('49', plain,
% 1.21/1.42      (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2))
% 1.21/1.42         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('split', [status(esa)], ['0'])).
% 1.21/1.42  thf(d13_relat_1, axiom,
% 1.21/1.42    (![A:$i]:
% 1.21/1.42     ( ( v1_relat_1 @ A ) =>
% 1.21/1.42       ( ![B:$i,C:$i]:
% 1.21/1.42         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 1.21/1.42           ( ![D:$i]:
% 1.21/1.42             ( ( r2_hidden @ D @ C ) <=>
% 1.21/1.42               ( ?[E:$i]:
% 1.21/1.42                 ( ( r2_hidden @ E @ B ) & 
% 1.21/1.42                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 1.21/1.42  thf('50', plain,
% 1.21/1.42      (![X17 : $i, X18 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 1.21/1.42         (((X20) != (k9_relat_1 @ X18 @ X17))
% 1.21/1.42          | (r2_hidden @ X22 @ X20)
% 1.21/1.42          | ~ (r2_hidden @ (k4_tarski @ X23 @ X22) @ X18)
% 1.21/1.42          | ~ (r2_hidden @ X23 @ X17)
% 1.21/1.42          | ~ (v1_relat_1 @ X18))),
% 1.21/1.42      inference('cnf', [status(esa)], [d13_relat_1])).
% 1.21/1.42  thf('51', plain,
% 1.21/1.42      (![X17 : $i, X18 : $i, X22 : $i, X23 : $i]:
% 1.21/1.42         (~ (v1_relat_1 @ X18)
% 1.21/1.42          | ~ (r2_hidden @ X23 @ X17)
% 1.21/1.42          | ~ (r2_hidden @ (k4_tarski @ X23 @ X22) @ X18)
% 1.21/1.42          | (r2_hidden @ X22 @ (k9_relat_1 @ X18 @ X17)))),
% 1.21/1.42      inference('simplify', [status(thm)], ['50'])).
% 1.21/1.42  thf('52', plain,
% 1.21/1.42      ((![X0 : $i]:
% 1.21/1.42          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 1.21/1.42           | ~ (r2_hidden @ sk_F @ X0)
% 1.21/1.42           | ~ (v1_relat_1 @ sk_D_2)))
% 1.21/1.42         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['49', '51'])).
% 1.21/1.42  thf('53', plain, ((v1_relat_1 @ sk_D_2)),
% 1.21/1.42      inference('demod', [status(thm)], ['14', '15'])).
% 1.21/1.42  thf('54', plain,
% 1.21/1.42      ((![X0 : $i]:
% 1.21/1.42          ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ X0))
% 1.21/1.42           | ~ (r2_hidden @ sk_F @ X0)))
% 1.21/1.42         <= (((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('demod', [status(thm)], ['52', '53'])).
% 1.21/1.42  thf('55', plain,
% 1.21/1.42      (((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (((r2_hidden @ sk_F @ sk_B)) & 
% 1.21/1.42             ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['48', '54'])).
% 1.21/1.42  thf('56', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         ((k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ X0)
% 1.21/1.42           = (k9_relat_1 @ sk_D_2 @ X0))),
% 1.21/1.42      inference('sup-', [status(thm)], ['4', '5'])).
% 1.21/1.42  thf('57', plain,
% 1.21/1.42      ((~ (r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (~
% 1.21/1.42             ((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('split', [status(esa)], ['29'])).
% 1.21/1.42  thf('58', plain,
% 1.21/1.42      ((~ (r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_B)))
% 1.21/1.42         <= (~
% 1.21/1.42             ((r2_hidden @ sk_E_2 @ 
% 1.21/1.42               (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B))))),
% 1.21/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.21/1.42  thf('59', plain,
% 1.21/1.42      (~ ((r2_hidden @ sk_F @ sk_B)) | 
% 1.21/1.42       ~ ((r2_hidden @ (k4_tarski @ sk_F @ sk_E_2) @ sk_D_2)) | 
% 1.21/1.42       ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_C_1 @ sk_A @ sk_D_2 @ sk_B)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['55', '58'])).
% 1.21/1.42  thf('60', plain, ($false),
% 1.21/1.42      inference('sat_resolution*', [status(thm)],
% 1.21/1.42                ['1', '3', '38', '45', '46', '47', '59'])).
% 1.21/1.42  
% 1.21/1.42  % SZS output end Refutation
% 1.21/1.42  
% 1.21/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
