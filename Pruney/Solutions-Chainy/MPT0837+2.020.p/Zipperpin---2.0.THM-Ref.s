%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0DEJvz0IJl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 126 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  674 (1506 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X28: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X17 @ X15 @ X16 ) @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X28: $i] :
        ( ~ ( m1_subset_1 @ X28 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X17 @ X15 ) )
      | ( r2_hidden @ ( sk_D_2 @ X17 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k1_relat_1 @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X19 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('31',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( m1_subset_1 @ X28 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X28 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k2_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k2_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0DEJvz0IJl
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 96 iterations in 0.103s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.56  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(t48_relset_1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.56               ( ![D:$i]:
% 0.20/0.56                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.56                   ( ?[E:$i]:
% 0.20/0.56                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.56                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.56                  ( ![D:$i]:
% 0.20/0.56                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.20/0.56                      ( ?[E:$i]:
% 0.20/0.56                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.20/0.56                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (![X28 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1)
% 0.20/0.56          | ~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((![X28 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1))) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.56         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.20/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)
% 0.20/0.56        | (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.56  thf(t146_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X18 : $i]:
% 0.20/0.56         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.20/0.56          | ~ (v1_relat_1 @ X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.56  thf(t143_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ C ) =>
% 0.20/0.56       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.56         ( ?[D:$i]:
% 0.20/0.56           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.56             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.56             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X17 @ X15 @ X16) @ X16) @ X17)
% 0.20/0.56          | ~ (v1_relat_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | (r2_hidden @ 
% 0.20/0.56             (k4_tarski @ (sk_D_2 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r2_hidden @ 
% 0.20/0.56           (k4_tarski @ (sk_D_2 @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.56         | (r2_hidden @ 
% 0.20/0.56            (k4_tarski @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56             sk_D_3) @ 
% 0.20/0.56            sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc2_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.56          | (v1_relat_1 @ X3)
% 0.20/0.56          | ~ (v1_relat_1 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf(fc6_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.56  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (((r2_hidden @ 
% 0.20/0.56         (k4_tarski @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56          sk_D_3) @ 
% 0.20/0.56         sk_C_1))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((![X28 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1)))
% 0.20/0.56         <= ((![X28 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56           sk_B))
% 0.20/0.56         <= ((![X28 : $i]:
% 0.20/0.56                (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56                 | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1))) & 
% 0.20/0.56             ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X18 : $i]:
% 0.20/0.56         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.20/0.56          | ~ (v1_relat_1 @ X18))),
% 0.20/0.56      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X16 @ (k9_relat_1 @ X17 @ X15))
% 0.20/0.56          | (r2_hidden @ (sk_D_2 @ X17 @ X15 @ X16) @ X15)
% 0.20/0.56          | ~ (v1_relat_1 @ X17))),
% 0.20/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | (r2_hidden @ (sk_D_2 @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.20/0.56             (k1_relat_1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r2_hidden @ (sk_D_2 @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.20/0.56           (k1_relat_1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.56         | (r2_hidden @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56            (k1_relat_1 @ sk_C_1))))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.56  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56         (k1_relat_1 @ sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (k1_relset_1 @ X19 @ X20 @ X21) @ (k1_zfmisc_1 @ X19))
% 0.20/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.56         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.20/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['31', '34'])).
% 0.20/0.56  thf(t4_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.56          | (m1_subset_1 @ X0 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ sk_B)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_D_3) @ 
% 0.20/0.56         sk_B))
% 0.20/0.56         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (~
% 0.20/0.56       (![X28 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ X28 @ sk_B)
% 0.20/0.56           | ~ (r2_hidden @ (k4_tarski @ X28 @ sk_D_3) @ sk_C_1))) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.20/0.56       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))
% 0.20/0.56         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.20/0.56      inference('split', [status(esa)], ['5'])).
% 0.20/0.56  thf(d5_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.20/0.56          | (r2_hidden @ X6 @ X8)
% 0.20/0.56          | ((X8) != (k2_relat_1 @ X7)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         ((r2_hidden @ X6 @ (k2_relat_1 @ X7))
% 0.20/0.56          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.20/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.56         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.20/0.56       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '47'])).
% 0.20/0.56  thf('49', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '48'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
