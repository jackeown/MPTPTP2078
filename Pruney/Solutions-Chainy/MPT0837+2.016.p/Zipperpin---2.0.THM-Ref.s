%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sWuAGq84Xd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:56 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 289 expanded)
%              Number of leaves         :   30 (  97 expanded)
%              Depth                    :   13
%              Number of atoms          :  732 (3153 expanded)
%              Number of equality atoms :   15 (  47 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ( X7
       != ( k2_relat_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ ( k2_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X6 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('34',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D_2 @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','40'])).

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
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('48',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X27: $i] :
        ( ~ ( m1_subset_1 @ X27 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ! [X27: $i] :
          ( ~ ( m1_subset_1 @ X27 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X27 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','44','45','46','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sWuAGq84Xd
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 103 iterations in 0.064s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.34/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(t48_relset_1, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.52           ( ![C:$i]:
% 0.34/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.52               ( ![D:$i]:
% 0.34/0.52                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.34/0.52                   ( ?[E:$i]:
% 0.34/0.52                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.34/0.52                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.34/0.52              ( ![C:$i]:
% 0.34/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.34/0.52                  ( ![D:$i]:
% 0.34/0.52                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.34/0.52                      ( ?[E:$i]:
% 0.34/0.52                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.34/0.52                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)
% 0.34/0.52        | (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf(d5_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.34/0.52       ( ![C:$i]:
% 0.34/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.34/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.34/0.52         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6)
% 0.34/0.52          | (r2_hidden @ X5 @ X7)
% 0.34/0.52          | ((X7) != (k2_relat_1 @ X6)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.34/0.52         ((r2_hidden @ X5 @ (k2_relat_1 @ X6))
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X6))),
% 0.34/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.34/0.52         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.34/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.34/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X27 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52          | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1)
% 0.34/0.52          | ~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      ((~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.34/0.52         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      ((~ (r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['7', '9'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))) | 
% 0.34/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['4', '10'])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relset_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.52         ((v4_relat_1 @ X21 @ X22)
% 0.34/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.52  thf('15', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.34/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.34/0.52  thf(t209_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.52       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X19 : $i, X20 : $i]:
% 0.34/0.52         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.34/0.52          | ~ (v4_relat_1 @ X19 @ X20)
% 0.34/0.52          | ~ (v1_relat_1 @ X19))),
% 0.34/0.52      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(cc2_relat_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.34/0.52          | (v1_relat_1 @ X2)
% 0.34/0.52          | ~ (v1_relat_1 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.34/0.52  thf(fc6_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.34/0.52  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('23', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['17', '22'])).
% 0.34/0.52  thf(t148_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X17 : $i, X18 : $i]:
% 0.34/0.52         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.34/0.52          | ~ (v1_relat_1 @ X17))),
% 0.34/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))
% 0.34/0.52        | ~ (v1_relat_1 @ sk_C_1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('27', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf(t143_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ C ) =>
% 0.34/0.52       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.34/0.52         ( ?[D:$i]:
% 0.34/0.52           ( ( r2_hidden @ D @ B ) & 
% 0.34/0.52             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.34/0.52             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X16 @ X14 @ X15) @ X15) @ X16)
% 0.34/0.52          | ~ (v1_relat_1 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | ~ (v1_relat_1 @ sk_C_1)
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.34/0.52             sk_C_1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.52  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.34/0.52             sk_C_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (((r2_hidden @ 
% 0.34/0.52         (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_D_3) @ sk_C_1))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['12', '31'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      ((![X27 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1)))
% 0.34/0.52         <= ((![X27 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= ((![X27 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) & 
% 0.34/0.52             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf('36', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.34/0.52          | (r2_hidden @ (sk_D_2 @ X16 @ X14 @ X15) @ X14)
% 0.34/0.52          | ~ (v1_relat_1 @ X16))),
% 0.34/0.52      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | ~ (v1_relat_1 @ sk_C_1)
% 0.34/0.52          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.34/0.52  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.34/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['35', '40'])).
% 0.34/0.52  thf(t1_subset, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (~
% 0.34/0.52       (![X27 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) | 
% 0.34/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['34', '43'])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))) | 
% 0.34/0.52       ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      ((![X27 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) | 
% 0.34/0.52       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('47', plain,
% 0.34/0.52      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.52  thf('48', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('split', [status(esa)], ['0'])).
% 0.34/0.52  thf('49', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.34/0.52  thf('50', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.34/0.52             sk_C_1))),
% 0.34/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.52  thf('51', plain,
% 0.34/0.52      (((r2_hidden @ 
% 0.34/0.52         (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_D_3) @ sk_C_1))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.34/0.52  thf('52', plain,
% 0.34/0.52      ((![X27 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1)))
% 0.34/0.52         <= ((![X27 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))))),
% 0.34/0.52      inference('split', [status(esa)], ['8'])).
% 0.34/0.52  thf('53', plain,
% 0.34/0.52      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= ((![X27 : $i]:
% 0.34/0.52                (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52                 | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) & 
% 0.34/0.52             ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.34/0.52  thf('54', plain,
% 0.34/0.52      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.34/0.52  thf('55', plain,
% 0.34/0.52      (![X0 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.34/0.52          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.34/0.52  thf('56', plain,
% 0.34/0.52      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.34/0.52  thf('57', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t1_subset])).
% 0.34/0.52  thf('58', plain,
% 0.34/0.52      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.34/0.52         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.52  thf('59', plain,
% 0.34/0.52      (~
% 0.34/0.52       (![X27 : $i]:
% 0.34/0.52          (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.52           | ~ (r2_hidden @ (k4_tarski @ X27 @ sk_D_3) @ sk_C_1))) | 
% 0.34/0.52       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.34/0.52      inference('demod', [status(thm)], ['53', '58'])).
% 0.34/0.52  thf('60', plain, ($false),
% 0.34/0.52      inference('sat_resolution*', [status(thm)],
% 0.34/0.52                ['11', '44', '45', '46', '59'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
