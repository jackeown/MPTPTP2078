%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCneB0Uada

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 6.27s
% Output     : Refutation 6.27s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 201 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  856 (2350 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('16',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X20 @ X18 @ X19 ) @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_D_1 ) @ sk_D_1 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X38: $i] :
      ( ~ ( m1_subset_1 @ X38 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X20 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X20 @ X18 @ X19 ) @ X18 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_D_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('45',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) )
   <= ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
    | ~ ! [X38: $i] :
          ( ~ ( m1_subset_1 @ X38 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
    | ! [X38: $i] :
        ( ~ ( m1_subset_1 @ X38 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X38 @ sk_D_1 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('53',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('67',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_1 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['36','51','52','53','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aCneB0Uada
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.27/6.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.27/6.47  % Solved by: fo/fo7.sh
% 6.27/6.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.27/6.47  % done 5073 iterations in 6.026s
% 6.27/6.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.27/6.47  % SZS output start Refutation
% 6.27/6.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.27/6.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.27/6.47  thf(sk_B_type, type, sk_B: $i).
% 6.27/6.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.27/6.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.27/6.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.27/6.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 6.27/6.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.27/6.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.27/6.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.27/6.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.27/6.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.27/6.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.27/6.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.27/6.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 6.27/6.47  thf(sk_A_type, type, sk_A: $i).
% 6.27/6.47  thf(sk_E_type, type, sk_E: $i).
% 6.27/6.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.27/6.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.27/6.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.27/6.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.27/6.47  thf(t48_relset_1, conjecture,
% 6.27/6.47    (![A:$i]:
% 6.27/6.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.27/6.47       ( ![B:$i]:
% 6.27/6.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.27/6.47           ( ![C:$i]:
% 6.27/6.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 6.27/6.47               ( ![D:$i]:
% 6.27/6.47                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 6.27/6.47                   ( ?[E:$i]:
% 6.27/6.47                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 6.27/6.47                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 6.27/6.47  thf(zf_stmt_0, negated_conjecture,
% 6.27/6.47    (~( ![A:$i]:
% 6.27/6.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.27/6.47          ( ![B:$i]:
% 6.27/6.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 6.27/6.47              ( ![C:$i]:
% 6.27/6.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 6.27/6.47                  ( ![D:$i]:
% 6.27/6.47                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 6.27/6.47                      ( ?[E:$i]:
% 6.27/6.47                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 6.27/6.47                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 6.27/6.47    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 6.27/6.47  thf('0', plain,
% 6.27/6.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.27/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.47  thf(redefinition_k2_relset_1, axiom,
% 6.27/6.47    (![A:$i,B:$i,C:$i]:
% 6.27/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.27/6.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.27/6.47  thf('1', plain,
% 6.27/6.47      (![X31 : $i, X32 : $i, X33 : $i]:
% 6.27/6.47         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 6.27/6.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 6.27/6.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.27/6.47  thf('2', plain,
% 6.27/6.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 6.27/6.47      inference('sup-', [status(thm)], ['0', '1'])).
% 6.27/6.47  thf('3', plain,
% 6.27/6.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)
% 6.27/6.47        | (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 6.27/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.47  thf('4', plain,
% 6.27/6.47      (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 6.27/6.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.47      inference('split', [status(esa)], ['3'])).
% 6.27/6.47  thf('5', plain,
% 6.27/6.47      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C_1)))
% 6.27/6.47         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.47      inference('sup+', [status(thm)], ['2', '4'])).
% 6.27/6.47  thf('6', plain,
% 6.27/6.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.27/6.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.47  thf(cc2_relset_1, axiom,
% 6.27/6.47    (![A:$i,B:$i,C:$i]:
% 6.27/6.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.27/6.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.27/6.47  thf('7', plain,
% 6.27/6.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.27/6.47         ((v4_relat_1 @ X28 @ X29)
% 6.27/6.48          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 6.27/6.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.27/6.48  thf('8', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 6.27/6.48      inference('sup-', [status(thm)], ['6', '7'])).
% 6.27/6.48  thf(t209_relat_1, axiom,
% 6.27/6.48    (![A:$i,B:$i]:
% 6.27/6.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.27/6.48       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 6.27/6.48  thf('9', plain,
% 6.27/6.48      (![X23 : $i, X24 : $i]:
% 6.27/6.48         (((X23) = (k7_relat_1 @ X23 @ X24))
% 6.27/6.48          | ~ (v4_relat_1 @ X23 @ X24)
% 6.27/6.48          | ~ (v1_relat_1 @ X23))),
% 6.27/6.48      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.27/6.48  thf('10', plain,
% 6.27/6.48      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['8', '9'])).
% 6.27/6.48  thf('11', plain,
% 6.27/6.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.27/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.48  thf(cc1_relset_1, axiom,
% 6.27/6.48    (![A:$i,B:$i,C:$i]:
% 6.27/6.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.27/6.48       ( v1_relat_1 @ C ) ))).
% 6.27/6.48  thf('12', plain,
% 6.27/6.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.27/6.48         ((v1_relat_1 @ X25)
% 6.27/6.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 6.27/6.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.27/6.48  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 6.27/6.48      inference('sup-', [status(thm)], ['11', '12'])).
% 6.27/6.48  thf('14', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 6.27/6.48      inference('demod', [status(thm)], ['10', '13'])).
% 6.27/6.48  thf(t148_relat_1, axiom,
% 6.27/6.48    (![A:$i,B:$i]:
% 6.27/6.48     ( ( v1_relat_1 @ B ) =>
% 6.27/6.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.27/6.48  thf('15', plain,
% 6.27/6.48      (![X21 : $i, X22 : $i]:
% 6.27/6.48         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 6.27/6.48          | ~ (v1_relat_1 @ X21))),
% 6.27/6.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.27/6.48  thf('16', plain,
% 6.27/6.48      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))
% 6.27/6.48        | ~ (v1_relat_1 @ sk_C_1))),
% 6.27/6.48      inference('sup+', [status(thm)], ['14', '15'])).
% 6.27/6.48  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 6.27/6.48      inference('sup-', [status(thm)], ['11', '12'])).
% 6.27/6.48  thf('18', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 6.27/6.48      inference('demod', [status(thm)], ['16', '17'])).
% 6.27/6.48  thf(t143_relat_1, axiom,
% 6.27/6.48    (![A:$i,B:$i,C:$i]:
% 6.27/6.48     ( ( v1_relat_1 @ C ) =>
% 6.27/6.48       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 6.27/6.48         ( ?[D:$i]:
% 6.27/6.48           ( ( r2_hidden @ D @ B ) & 
% 6.27/6.48             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 6.27/6.48             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 6.27/6.48  thf('19', plain,
% 6.27/6.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 6.27/6.48          | (r2_hidden @ (k4_tarski @ (sk_D @ X20 @ X18 @ X19) @ X19) @ X20)
% 6.27/6.48          | ~ (v1_relat_1 @ X20))),
% 6.27/6.48      inference('cnf', [status(esa)], [t143_relat_1])).
% 6.27/6.48  thf('20', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 6.27/6.48          | ~ (v1_relat_1 @ sk_C_1)
% 6.27/6.48          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 6.27/6.48             sk_C_1))),
% 6.27/6.48      inference('sup-', [status(thm)], ['18', '19'])).
% 6.27/6.48  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 6.27/6.48      inference('sup-', [status(thm)], ['11', '12'])).
% 6.27/6.48  thf('22', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 6.27/6.48          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 6.27/6.48             sk_C_1))),
% 6.27/6.48      inference('demod', [status(thm)], ['20', '21'])).
% 6.27/6.48  thf('23', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_D_1) @ sk_D_1) @ 
% 6.27/6.48         sk_C_1))
% 6.27/6.48         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['5', '22'])).
% 6.27/6.48  thf('24', plain,
% 6.27/6.48      (![X38 : $i]:
% 6.27/6.48         (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48          | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)
% 6.27/6.48          | ~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 6.27/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.48  thf('25', plain,
% 6.27/6.48      ((![X38 : $i]:
% 6.27/6.48          (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)))
% 6.27/6.48         <= ((![X38 : $i]:
% 6.27/6.48                (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1))))),
% 6.27/6.48      inference('split', [status(esa)], ['24'])).
% 6.27/6.48  thf('26', plain,
% 6.27/6.48      ((~ (m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_D_1) @ sk_B))
% 6.27/6.48         <= ((![X38 : $i]:
% 6.27/6.48                (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1))) & 
% 6.27/6.48             ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['23', '25'])).
% 6.27/6.48  thf('27', plain,
% 6.27/6.48      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C_1)))
% 6.27/6.48         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup+', [status(thm)], ['2', '4'])).
% 6.27/6.48  thf('28', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 6.27/6.48      inference('demod', [status(thm)], ['16', '17'])).
% 6.27/6.48  thf('29', plain,
% 6.27/6.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X19 @ (k9_relat_1 @ X20 @ X18))
% 6.27/6.48          | (r2_hidden @ (sk_D @ X20 @ X18 @ X19) @ X18)
% 6.27/6.48          | ~ (v1_relat_1 @ X20))),
% 6.27/6.48      inference('cnf', [status(esa)], [t143_relat_1])).
% 6.27/6.48  thf('30', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 6.27/6.48          | ~ (v1_relat_1 @ sk_C_1)
% 6.27/6.48          | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 6.27/6.48      inference('sup-', [status(thm)], ['28', '29'])).
% 6.27/6.48  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 6.27/6.48      inference('sup-', [status(thm)], ['11', '12'])).
% 6.27/6.48  thf('32', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 6.27/6.48          | (r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 6.27/6.48      inference('demod', [status(thm)], ['30', '31'])).
% 6.27/6.48  thf('33', plain,
% 6.27/6.48      (((r2_hidden @ (sk_D @ sk_C_1 @ sk_B @ sk_D_1) @ sk_B))
% 6.27/6.48         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['27', '32'])).
% 6.27/6.48  thf(t1_subset, axiom,
% 6.27/6.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 6.27/6.48  thf('34', plain,
% 6.27/6.48      (![X12 : $i, X13 : $i]:
% 6.27/6.48         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 6.27/6.48      inference('cnf', [status(esa)], [t1_subset])).
% 6.27/6.48  thf('35', plain,
% 6.27/6.48      (((m1_subset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_D_1) @ sk_B))
% 6.27/6.48         <= (((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['33', '34'])).
% 6.27/6.48  thf('36', plain,
% 6.27/6.48      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))) | 
% 6.27/6.48       ~
% 6.27/6.48       (![X38 : $i]:
% 6.27/6.48          (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('demod', [status(thm)], ['26', '35'])).
% 6.27/6.48  thf('37', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('split', [status(esa)], ['3'])).
% 6.27/6.48  thf('38', plain,
% 6.27/6.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.27/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.48  thf(t3_subset, axiom,
% 6.27/6.48    (![A:$i,B:$i]:
% 6.27/6.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.27/6.48  thf('39', plain,
% 6.27/6.48      (![X14 : $i, X15 : $i]:
% 6.27/6.48         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 6.27/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.27/6.48  thf('40', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))),
% 6.27/6.48      inference('sup-', [status(thm)], ['38', '39'])).
% 6.27/6.48  thf(d3_tarski, axiom,
% 6.27/6.48    (![A:$i,B:$i]:
% 6.27/6.48     ( ( r1_tarski @ A @ B ) <=>
% 6.27/6.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.27/6.48  thf('41', plain,
% 6.27/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ X1)
% 6.27/6.48          | (r2_hidden @ X0 @ X2)
% 6.27/6.48          | ~ (r1_tarski @ X1 @ X2))),
% 6.27/6.48      inference('cnf', [status(esa)], [d3_tarski])).
% 6.27/6.48  thf('42', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 6.27/6.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 6.27/6.48      inference('sup-', [status(thm)], ['40', '41'])).
% 6.27/6.48  thf('43', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['37', '42'])).
% 6.27/6.48  thf(l54_zfmisc_1, axiom,
% 6.27/6.48    (![A:$i,B:$i,C:$i,D:$i]:
% 6.27/6.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 6.27/6.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 6.27/6.48  thf('44', plain,
% 6.27/6.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 6.27/6.48         ((r2_hidden @ X7 @ X8)
% 6.27/6.48          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 6.27/6.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.27/6.48  thf('45', plain,
% 6.27/6.48      (((r2_hidden @ sk_E @ sk_B))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['43', '44'])).
% 6.27/6.48  thf('46', plain,
% 6.27/6.48      (![X12 : $i, X13 : $i]:
% 6.27/6.48         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 6.27/6.48      inference('cnf', [status(esa)], [t1_subset])).
% 6.27/6.48  thf('47', plain,
% 6.27/6.48      (((m1_subset_1 @ sk_E @ sk_B))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['45', '46'])).
% 6.27/6.48  thf('48', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('split', [status(esa)], ['3'])).
% 6.27/6.48  thf('49', plain,
% 6.27/6.48      ((![X38 : $i]:
% 6.27/6.48          (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)))
% 6.27/6.48         <= ((![X38 : $i]:
% 6.27/6.48                (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1))))),
% 6.27/6.48      inference('split', [status(esa)], ['24'])).
% 6.27/6.48  thf('50', plain,
% 6.27/6.48      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 6.27/6.48         <= ((![X38 : $i]:
% 6.27/6.48                (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48                 | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1))) & 
% 6.27/6.48             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['48', '49'])).
% 6.27/6.48  thf('51', plain,
% 6.27/6.48      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)) | 
% 6.27/6.48       ~
% 6.27/6.48       (![X38 : $i]:
% 6.27/6.48          (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['47', '50'])).
% 6.27/6.48  thf('52', plain,
% 6.27/6.48      (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))) | 
% 6.27/6.48       (![X38 : $i]:
% 6.27/6.48          (~ (m1_subset_1 @ X38 @ sk_B)
% 6.27/6.48           | ~ (r2_hidden @ (k4_tarski @ X38 @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('split', [status(esa)], ['24'])).
% 6.27/6.48  thf('53', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)) | 
% 6.27/6.48       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 6.27/6.48      inference('split', [status(esa)], ['3'])).
% 6.27/6.48  thf('54', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('split', [status(esa)], ['3'])).
% 6.27/6.48  thf(d10_xboole_0, axiom,
% 6.27/6.48    (![A:$i,B:$i]:
% 6.27/6.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.27/6.48  thf('55', plain,
% 6.27/6.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 6.27/6.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.27/6.48  thf('56', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 6.27/6.48      inference('simplify', [status(thm)], ['55'])).
% 6.27/6.48  thf('57', plain,
% 6.27/6.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 6.27/6.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.27/6.48  thf(t14_relset_1, axiom,
% 6.27/6.48    (![A:$i,B:$i,C:$i,D:$i]:
% 6.27/6.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 6.27/6.48       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 6.27/6.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 6.27/6.48  thf('58', plain,
% 6.27/6.48      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 6.27/6.48         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 6.27/6.48          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 6.27/6.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 6.27/6.48      inference('cnf', [status(esa)], [t14_relset_1])).
% 6.27/6.48  thf('59', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 6.27/6.48          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ X0))),
% 6.27/6.48      inference('sup-', [status(thm)], ['57', '58'])).
% 6.27/6.48  thf('60', plain,
% 6.27/6.48      ((m1_subset_1 @ sk_C_1 @ 
% 6.27/6.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['56', '59'])).
% 6.27/6.48  thf('61', plain,
% 6.27/6.48      (![X14 : $i, X15 : $i]:
% 6.27/6.48         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 6.27/6.48      inference('cnf', [status(esa)], [t3_subset])).
% 6.27/6.48  thf('62', plain,
% 6.27/6.48      ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['60', '61'])).
% 6.27/6.48  thf('63', plain,
% 6.27/6.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.27/6.48         (~ (r2_hidden @ X0 @ X1)
% 6.27/6.48          | (r2_hidden @ X0 @ X2)
% 6.27/6.48          | ~ (r1_tarski @ X1 @ X2))),
% 6.27/6.48      inference('cnf', [status(esa)], [d3_tarski])).
% 6.27/6.48  thf('64', plain,
% 6.27/6.48      (![X0 : $i]:
% 6.27/6.48         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 6.27/6.48          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 6.27/6.48      inference('sup-', [status(thm)], ['62', '63'])).
% 6.27/6.48  thf('65', plain,
% 6.27/6.48      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ 
% 6.27/6.48         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_C_1))))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['54', '64'])).
% 6.27/6.48  thf('66', plain,
% 6.27/6.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 6.27/6.48         ((r2_hidden @ X9 @ X10)
% 6.27/6.48          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 6.27/6.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 6.27/6.48  thf('67', plain,
% 6.27/6.48      (((r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C_1)))
% 6.27/6.48         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['65', '66'])).
% 6.27/6.48  thf('68', plain,
% 6.27/6.48      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 6.27/6.48      inference('sup-', [status(thm)], ['0', '1'])).
% 6.27/6.48  thf('69', plain,
% 6.27/6.48      ((~ (r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 6.27/6.48         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('split', [status(esa)], ['24'])).
% 6.27/6.48  thf('70', plain,
% 6.27/6.48      ((~ (r2_hidden @ sk_D_1 @ (k2_relat_1 @ sk_C_1)))
% 6.27/6.48         <= (~ ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 6.27/6.48      inference('sup-', [status(thm)], ['68', '69'])).
% 6.27/6.48  thf('71', plain,
% 6.27/6.48      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_1) @ sk_C_1)) | 
% 6.27/6.48       ((r2_hidden @ sk_D_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 6.27/6.48      inference('sup-', [status(thm)], ['67', '70'])).
% 6.27/6.48  thf('72', plain, ($false),
% 6.27/6.48      inference('sat_resolution*', [status(thm)],
% 6.27/6.48                ['36', '51', '52', '53', '71'])).
% 6.27/6.48  
% 6.27/6.48  % SZS output end Refutation
% 6.27/6.48  
% 6.27/6.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
