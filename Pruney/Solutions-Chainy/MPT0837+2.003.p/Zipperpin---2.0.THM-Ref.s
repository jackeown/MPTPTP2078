%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPN9b3jUJ6

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 195 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  827 (2315 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) )
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
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
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X34 @ sk_D_1 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('56',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('63',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['24'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['36','49','50','51','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uPN9b3jUJ6
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 502 iterations in 0.234s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(t48_relset_1, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.69               ( ![D:$i]:
% 0.45/0.69                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.45/0.69                   ( ?[E:$i]:
% 0.45/0.69                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.45/0.69                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69          ( ![B:$i]:
% 0.45/0.69            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.69              ( ![C:$i]:
% 0.45/0.69                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.69                  ( ![D:$i]:
% 0.45/0.69                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.45/0.69                      ( ?[E:$i]:
% 0.45/0.69                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.45/0.69                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.69         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.45/0.69          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.69  thf('2', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)
% 0.45/0.69        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('split', [status(esa)], ['3'])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['2', '4'])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.69         ((v4_relat_1 @ X24 @ X25)
% 0.45/0.69          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.69  thf('8', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.45/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.69  thf(t209_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.69       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X19 : $i, X20 : $i]:
% 0.45/0.69         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.45/0.69          | ~ (v4_relat_1 @ X19 @ X20)
% 0.45/0.69          | ~ (v1_relat_1 @ X19))),
% 0.45/0.69      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( v1_relat_1 @ C ) ))).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.69         ((v1_relat_1 @ X21)
% 0.45/0.69          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.69  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('14', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['10', '13'])).
% 0.45/0.69  thf(t148_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X17 : $i, X18 : $i]:
% 0.45/0.69         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.45/0.69          | ~ (v1_relat_1 @ X17))),
% 0.45/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('18', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf(t143_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ C ) =>
% 0.45/0.69       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.69         ( ?[D:$i]:
% 0.45/0.69           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.69             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.69             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.45/0.69          | (r2_hidden @ (k4_tarski @ (sk_D @ X16 @ X14 @ X15) @ X15) @ X16)
% 0.45/0.69          | ~ (v1_relat_1 @ X16))),
% 0.45/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.45/0.69          | ~ (v1_relat_1 @ sk_C)
% 0.45/0.69          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.69  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.45/0.69          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ X0) @ X0) @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 0.45/0.69         sk_C))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['5', '22'])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (![X34 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)
% 0.45/0.69          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      ((![X34 : $i]:
% 0.45/0.69          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)))
% 0.45/0.69         <= ((![X34 : $i]:
% 0.45/0.69                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C))))),
% 0.45/0.69      inference('split', [status(esa)], ['24'])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      ((~ (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.45/0.69         <= ((![X34 : $i]:
% 0.45/0.69                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C))) & 
% 0.45/0.69             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['23', '25'])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['2', '4'])).
% 0.45/0.69  thf('28', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.45/0.69          | (r2_hidden @ (sk_D @ X16 @ X14 @ X15) @ X14)
% 0.45/0.69          | ~ (v1_relat_1 @ X16))),
% 0.45/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.45/0.69          | ~ (v1_relat_1 @ sk_C)
% 0.45/0.69          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.45/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.69  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.45/0.69          | (r2_hidden @ (sk_D @ sk_C @ sk_B @ X0) @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['27', '32'])).
% 0.45/0.69  thf(t1_subset, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (((m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_D_1) @ sk_B))
% 0.45/0.69         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.45/0.69       ~
% 0.45/0.69       (![X34 : $i]:
% 0.45/0.69          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('demod', [status(thm)], ['26', '35'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('split', [status(esa)], ['3'])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(l3_subset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.69          | (r2_hidden @ X8 @ X10)
% 0.45/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.69      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.45/0.69          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['37', '40'])).
% 0.45/0.69  thf(l54_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.45/0.69       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.69         ((r2_hidden @ X3 @ X4)
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.45/0.69      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (((r2_hidden @ sk_E @ sk_B))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X11 : $i, X12 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_E @ sk_B))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('split', [status(esa)], ['3'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      ((![X34 : $i]:
% 0.45/0.69          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)))
% 0.45/0.69         <= ((![X34 : $i]:
% 0.45/0.69                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C))))),
% 0.45/0.69      inference('split', [status(esa)], ['24'])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.45/0.69         <= ((![X34 : $i]:
% 0.45/0.69                (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69                 | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C))) & 
% 0.45/0.69             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.45/0.69       ~
% 0.45/0.69       (![X34 : $i]:
% 0.45/0.69          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['45', '48'])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.45/0.69       (![X34 : $i]:
% 0.45/0.69          (~ (m1_subset_1 @ X34 @ sk_B)
% 0.45/0.69           | ~ (r2_hidden @ (k4_tarski @ X34 @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('split', [status(esa)], ['24'])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.45/0.69       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.45/0.69      inference('split', [status(esa)], ['3'])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('split', [status(esa)], ['3'])).
% 0.45/0.69  thf(d10_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.69  thf('54', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t14_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.45/0.69       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.45/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.69         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 0.45/0.69          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.45/0.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.45/0.69      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.45/0.69          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['54', '57'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.69          | (r2_hidden @ X8 @ X10)
% 0.45/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.45/0.69      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.45/0.69          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ 
% 0.45/0.69         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C))))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['52', '60'])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.69         ((r2_hidden @ X5 @ X6)
% 0.45/0.69          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.45/0.69      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.45/0.69         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.45/0.69         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('split', [status(esa)], ['24'])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      ((~ (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C)))
% 0.45/0.69         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C)) | 
% 0.45/0.69       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['63', '66'])).
% 0.45/0.69  thf('68', plain, ($false),
% 0.45/0.69      inference('sat_resolution*', [status(thm)],
% 0.45/0.69                ['36', '49', '50', '51', '67'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.53/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
