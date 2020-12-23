%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FM2aqiJLcm

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 172 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  719 (2265 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ sk_E @ ( k11_relat_1 @ sk_C_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_E @ ( k11_relat_1 @ sk_C_1 @ sk_D_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k11_relat_1 @ X3 @ X4 )
        = ( k9_relat_1 @ X3 @ ( k1_tarski @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_relat_1 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k11_relat_1 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k11_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('35',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('40',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ( X8
       != ( k1_relat_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('43',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X9 @ ( sk_D_1 @ X9 @ X7 ) ) @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ ( k11_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('46',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ ( k11_relat_1 @ sk_C_1 @ sk_D_2 ) ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('48',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ ( k11_relat_1 @ sk_C_1 @ sk_D_2 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k11_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('52',plain,
    ( ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) )
   <= ! [X29: $i] :
        ( ~ ( m1_subset_1 @ X29 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ! [X29: $i] :
          ( ~ ( m1_subset_1 @ X29 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X29 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['11','36','37','38','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FM2aqiJLcm
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 81 iterations in 0.067s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(t47_relset_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.51                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.51                     ( ?[E:$i]:
% 0.20/0.51                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.51                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.51                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.20/0.51                        ( ?[E:$i]:
% 0.20/0.51                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.20/0.51                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)
% 0.20/0.51        | (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(d4_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.20/0.51          | (r2_hidden @ X5 @ X8)
% 0.20/0.51          | ((X8) != (k1_relat_1 @ X7)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         ((r2_hidden @ X5 @ (k1_relat_1 @ X7))
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7))),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X29 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1)
% 0.20/0.51          | ~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.51         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.20/0.51       ~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(t204_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.51          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.51          | ~ (v1_relat_1 @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.51         | (r2_hidden @ sk_E @ (k11_relat_1 @ sk_C_1 @ sk_D_2))))
% 0.20/0.51         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(cc1_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( v1_relat_1 @ C ) ))).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.52         ((v1_relat_1 @ X15)
% 0.20/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.52  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((r2_hidden @ sk_E @ (k11_relat_1 @ sk_C_1 @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.52  thf(d16_relat_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X3 : $i, X4 : $i]:
% 0.20/0.52         (((k11_relat_1 @ X3 @ X4) = (k9_relat_1 @ X3 @ (k1_tarski @ X4)))
% 0.20/0.52          | ~ (v1_relat_1 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.52          | (m1_subset_1 @ (k7_relset_1 @ X19 @ X20 @ X18 @ X21) @ 
% 0.20/0.52             (k1_zfmisc_1 @ X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 0.20/0.52          (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.52          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0)
% 0.20/0.52           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k9_relat_1 @ sk_C_1 @ X0) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k11_relat_1 @ sk_C_1 @ X0) @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.52          | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup+', [status(thm)], ['19', '26'])).
% 0.20/0.52  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (m1_subset_1 @ (k11_relat_1 @ sk_C_1 @ X0) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.52  thf(t4_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.52          | (m1_subset_1 @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X1 @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ (k11_relat_1 @ sk_C_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_E @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((![X29 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) & 
% 0.20/0.52             (![X29 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X29 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.20/0.52       ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((![X29 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X8)
% 0.20/0.52          | (r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.20/0.52          | ((X8) != (k1_relat_1 @ X7)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X7 : $i, X9 : $i]:
% 0.20/0.52         ((r2_hidden @ (k4_tarski @ X9 @ (sk_D_1 @ X9 @ X7)) @ X7)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '43'])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ (k4_tarski @ X14 @ X12) @ X13)
% 0.20/0.52          | (r2_hidden @ X12 @ (k11_relat_1 @ X13 @ X14))
% 0.20/0.52          | ~ (v1_relat_1 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.52         | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ 
% 0.20/0.52            (k11_relat_1 @ sk_C_1 @ sk_D_2))))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ 
% 0.20/0.52         (k11_relat_1 @ sk_C_1 @ sk_D_2)))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X1 @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ (k11_relat_1 @ sk_C_1 @ X0)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '43'])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      ((![X29 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1)))
% 0.20/0.52         <= ((![X29 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.20/0.52         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.20/0.52             (![X29 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (~
% 0.20/0.52       (![X29 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X29 @ sk_B)
% 0.20/0.52           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X29) @ sk_C_1))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.52  thf('55', plain, ($false),
% 0.20/0.52      inference('sat_resolution*', [status(thm)],
% 0.20/0.52                ['11', '36', '37', '38', '54'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
