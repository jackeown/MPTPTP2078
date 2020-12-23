%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HnGlJDeQ9V

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 228 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :  779 (2659 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) )
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('49',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('53',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('54',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('57',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('58',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ X18 )
      | ( r2_hidden @ X17 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('60',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['11','12'])).

thf('62',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['44','55','56','57','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HnGlJDeQ9V
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 73 iterations in 0.029s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(t48_relset_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.49                   ( ?[E:$i]:
% 0.20/0.49                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.49                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.49                      ( ?[E:$i]:
% 0.20/0.49                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.49                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('2', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)
% 0.20/0.49        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X22 @ X23)
% 0.20/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(t209_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.20/0.49          | ~ (v4_relat_1 @ X14 @ X15)
% 0.20/0.49          | ~ (v1_relat_1 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( v1_relat_1 @ C ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X19)
% 0.20/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.49  thf(t148_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('18', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf(t143_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.20/0.49         sk_C))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X28 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)
% 0.20/0.49          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((![X28 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)))
% 0.20/0.49         <= ((![X28 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= ((![X28 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C))) & 
% 0.20/0.49             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.49  thf('28', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ (k1_relat_1 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ (k1_relat_1 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ (k1_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '32'])).
% 0.20/0.49  thf('34', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('38', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf(t4_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (m1_subset_1 @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.49       ~
% 0.20/0.49       (![X28 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['26', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf(t20_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.49           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.20/0.49          | (r2_hidden @ X16 @ (k1_relat_1 @ X18))
% 0.20/0.49          | ~ (v1_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_E @ (k1_relat_1 @ sk_C))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((m1_subset_1 @ sk_E @ sk_B))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      ((![X28 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)))
% 0.20/0.49         <= ((![X28 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['24'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.20/0.49         <= ((![X28 : $i]:
% 0.20/0.49                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C))) & 
% 0.20/0.49             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.20/0.49       ~
% 0.20/0.49       (![X28 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.49       (![X28 : $i]:
% 0.20/0.49          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.49           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['24'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.20/0.49       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['3'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ X18)
% 0.20/0.49          | (r2_hidden @ X17 @ (k2_relat_1 @ X18))
% 0.20/0.49          | ~ (v1_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((~ (v1_relat_1 @ sk_C) | (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C))))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.49  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['24'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      ((~ (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.20/0.49         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.20/0.49       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '65'])).
% 0.20/0.49  thf('67', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['44', '55', '56', '57', '66'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
