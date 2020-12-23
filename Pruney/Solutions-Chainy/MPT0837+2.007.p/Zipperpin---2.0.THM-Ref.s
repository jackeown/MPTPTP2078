%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WMcBdRBrBU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 201 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  848 (2336 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ X0 ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ X0 ) @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X36 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('53',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('55',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('66',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('68',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['36','49','50','51','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WMcBdRBrBU
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 946 iterations in 0.499s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.95  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.95  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.95  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.76/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.95  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(sk_E_type, type, sk_E: $i).
% 0.76/0.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.95  thf(t48_relset_1, conjecture,
% 0.76/0.95    (![A:$i]:
% 0.76/0.95     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.95       ( ![B:$i]:
% 0.76/0.95         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.95           ( ![C:$i]:
% 0.76/0.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.76/0.95               ( ![D:$i]:
% 0.76/0.95                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.76/0.95                   ( ?[E:$i]:
% 0.76/0.95                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.76/0.95                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i]:
% 0.76/0.95        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.76/0.95          ( ![B:$i]:
% 0.76/0.95            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.95              ( ![C:$i]:
% 0.76/0.95                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.76/0.95                  ( ![D:$i]:
% 0.76/0.95                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.76/0.95                      ( ?[E:$i]:
% 0.76/0.95                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.76/0.95                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.95  thf('1', plain,
% 0.76/0.95      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.95         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.76/0.95          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.76/0.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.95  thf('2', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)
% 0.76/0.95        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('split', [status(esa)], ['3'])).
% 0.76/0.95  thf('5', plain,
% 0.76/0.95      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['2', '4'])).
% 0.76/0.95  thf('6', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc2_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.95  thf('7', plain,
% 0.76/0.95      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.95         ((v4_relat_1 @ X26 @ X27)
% 0.76/0.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.95  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.76/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.95  thf(t209_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.95       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X21 : $i, X22 : $i]:
% 0.76/0.95         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.76/0.95          | ~ (v4_relat_1 @ X21 @ X22)
% 0.76/0.95          | ~ (v1_relat_1 @ X21))),
% 0.76/0.95      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc1_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95       ( v1_relat_1 @ C ) ))).
% 0.76/0.95  thf('12', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.95         ((v1_relat_1 @ X23)
% 0.76/0.95          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.95  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('14', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['10', '13'])).
% 0.76/0.95  thf(t148_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ B ) =>
% 0.76/0.95       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (![X19 : $i, X20 : $i]:
% 0.76/0.95         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.76/0.95          | ~ (v1_relat_1 @ X19))),
% 0.76/0.95      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.76/0.95        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.95      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.95  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('18', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.95  thf(t143_relat_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( v1_relat_1 @ C ) =>
% 0.76/0.95       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.76/0.95         ( ?[D:$i]:
% 0.76/0.95           ( ( r2_hidden @ D @ B ) & 
% 0.76/0.95             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.76/0.95             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.76/0.95          | ~ (v1_relat_1 @ X18))),
% 0.76/0.95      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.76/0.95  thf('20', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.76/0.95          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.95  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.76/0.95          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.76/0.95      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.76/0.95         sk_C))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['5', '22'])).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X36 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)
% 0.76/0.95          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('25', plain,
% 0.76/0.95      ((![X36 : $i]:
% 0.76/0.95          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)))
% 0.76/0.95         <= ((![X36 : $i]:
% 0.76/0.95                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C))))),
% 0.76/0.95      inference('split', [status(esa)], ['24'])).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.76/0.95         <= ((![X36 : $i]:
% 0.76/0.95                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C))) & 
% 0.76/0.95             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['23', '25'])).
% 0.76/0.95  thf('27', plain,
% 0.76/0.95      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['2', '4'])).
% 0.76/0.95  thf('28', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['16', '17'])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.76/0.95          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.76/0.95          | ~ (v1_relat_1 @ X18))),
% 0.76/0.95      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.76/0.95          | ~ (v1_relat_1 @ sk_C)
% 0.76/0.95          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.95  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.95      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.76/0.95          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.76/0.95      inference('demod', [status(thm)], ['30', '31'])).
% 0.76/0.95  thf('33', plain,
% 0.76/0.95      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['27', '32'])).
% 0.76/0.95  thf(t1_subset, axiom,
% 0.76/0.95    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X10 : $i, X11 : $i]:
% 0.76/0.95         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.76/0.95      inference('cnf', [status(esa)], [t1_subset])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.76/0.95       ~
% 0.76/0.95       (![X36 : $i]:
% 0.76/0.95          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('demod', [status(thm)], ['26', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['3'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(l3_subset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.76/0.95  thf('39', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X7 @ X8)
% 0.76/0.95          | (r2_hidden @ X7 @ X9)
% 0.76/0.95          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.76/0.95      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.76/0.95          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['37', '40'])).
% 0.76/0.95  thf(l54_zfmisc_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.76/0.95       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ X1)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.76/0.95      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.76/0.95  thf('43', plain,
% 0.76/0.95      (((r2_hidden @ sk_E @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      (![X10 : $i, X11 : $i]:
% 0.76/0.95         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.76/0.95      inference('cnf', [status(esa)], [t1_subset])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_E @ sk_B))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['3'])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      ((![X36 : $i]:
% 0.76/0.95          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)))
% 0.76/0.95         <= ((![X36 : $i]:
% 0.76/0.95                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C))))),
% 0.76/0.95      inference('split', [status(esa)], ['24'])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.76/0.95         <= ((![X36 : $i]:
% 0.76/0.95                (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95                 | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C))) & 
% 0.76/0.95             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.76/0.95       ~
% 0.76/0.95       (![X36 : $i]:
% 0.76/0.95          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['45', '48'])).
% 0.76/0.95  thf('50', plain,
% 0.76/0.95      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.76/0.95       (![X36 : $i]:
% 0.76/0.95          (~ (m1_subset_1 @ X36 @ sk_B)
% 0.76/0.95           | ~ (r2_hidden @ (k4_tarski @ X36 @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['24'])).
% 0.76/0.95  thf('51', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.76/0.95       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['3'])).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('split', [status(esa)], ['3'])).
% 0.76/0.95  thf(dt_k2_subset_1, axiom,
% 0.76/0.95    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.95  thf('53', plain,
% 0.76/0.95      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.76/0.95      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.76/0.95  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.76/0.95  thf('54', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.76/0.95      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.76/0.95  thf('55', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.76/0.95      inference('demod', [status(thm)], ['53', '54'])).
% 0.76/0.95  thf(t3_subset, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.95  thf('56', plain,
% 0.76/0.95      (![X12 : $i, X13 : $i]:
% 0.76/0.95         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.95  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.95      inference('sup-', [status(thm)], ['55', '56'])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(t14_relset_1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.76/0.95       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.76/0.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.76/0.95  thf('59', plain,
% 0.76/0.95      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.95         (~ (r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.76/0.95          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.76/0.95          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.76/0.95      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.76/0.95  thf('60', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.76/0.95          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['58', '59'])).
% 0.76/0.95  thf('61', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C @ 
% 0.76/0.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['57', '60'])).
% 0.76/0.95  thf('62', plain,
% 0.76/0.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X7 @ X8)
% 0.76/0.95          | (r2_hidden @ X7 @ X9)
% 0.76/0.95          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.76/0.95      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.76/0.95  thf('63', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.76/0.95          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['61', '62'])).
% 0.76/0.95  thf('64', plain,
% 0.76/0.95      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ 
% 0.76/0.95         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['52', '63'])).
% 0.76/0.95  thf('65', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.76/0.95         ((r2_hidden @ X2 @ X3)
% 0.76/0.95          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.76/0.95      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.76/0.95  thf('66', plain,
% 0.76/0.95      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.76/0.95         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['64', '65'])).
% 0.76/0.95  thf('67', plain,
% 0.76/0.95      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.76/0.95      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.95  thf('68', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.76/0.95         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('split', [status(esa)], ['24'])).
% 0.76/0.95  thf('69', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.76/0.95         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/0.95  thf('70', plain,
% 0.76/0.95      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.76/0.95       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['66', '69'])).
% 0.76/0.95  thf('71', plain, ($false),
% 0.76/0.95      inference('sat_resolution*', [status(thm)],
% 0.76/0.95                ['36', '49', '50', '51', '70'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
