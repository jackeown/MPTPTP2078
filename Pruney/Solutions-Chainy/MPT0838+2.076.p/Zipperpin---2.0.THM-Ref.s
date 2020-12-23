%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CHxT8j1EqO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 372 expanded)
%              Number of leaves         :   36 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  579 (3604 expanded)
%              Number of equality atoms :   47 ( 175 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X20 ) @ X21 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('16',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X33: $i] :
      ~ ( r2_hidden @ X33 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['20','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','32'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','38','39'])).

thf('41',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k7_relat_1 @ X22 @ X23 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('43',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('45',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('47',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('58',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('61',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CHxT8j1EqO
% 0.17/0.37  % Computer   : n014.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 85 iterations in 0.093s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(t49_relset_1, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.58                    ( ![D:$i]:
% 0.38/0.58                      ( ( m1_subset_1 @ D @ B ) =>
% 0.38/0.58                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.58              ( ![C:$i]:
% 0.38/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.58                       ( ![D:$i]:
% 0.38/0.58                         ( ( m1_subset_1 @ D @ B ) =>
% 0.38/0.58                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.58         ((v4_relat_1 @ X24 @ X25)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.58  thf('2', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf(t209_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.58       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.38/0.58          | ~ (v4_relat_1 @ X17 @ X18)
% 0.38/0.58          | ~ (v1_relat_1 @ X17))),
% 0.38/0.58      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc2_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.38/0.58          | (v1_relat_1 @ X11)
% 0.38/0.58          | ~ (v1_relat_1 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf(fc6_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.58  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['4', '9'])).
% 0.38/0.58  thf(t90_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.38/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         (((k1_relat_1 @ (k7_relat_1 @ X20 @ X21))
% 0.38/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X20) @ X21))
% 0.38/0.58          | ~ (v1_relat_1 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      ((((k1_relat_1 @ sk_C_1) = (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.58  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (((k1_relat_1 @ sk_C_1) = (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf(t7_xboole_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X33 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X33 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.58         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 0.38/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X33 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X33 @ (k2_relat_1 @ sk_C_1))
% 0.38/0.58          | ~ (m1_subset_1 @ X33 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['16', '19'])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.58         ((v5_relat_1 @ X24 @ X26)
% 0.38/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.58  thf('23', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.58  thf(d19_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i]:
% 0.38/0.58         (~ (v5_relat_1 @ X13 @ X14)
% 0.38/0.58          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.58  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.58  thf(t3_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X5 : $i, X7 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf(t4_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.58       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X8 @ X9)
% 0.38/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.38/0.58          | (m1_subset_1 @ X8 @ X10))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain, (![X33 : $i]: ~ (r2_hidden @ X33 @ (k2_relat_1 @ sk_C_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['20', '31'])).
% 0.38/0.58  thf('33', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '32'])).
% 0.38/0.58  thf(t64_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X19 : $i]:
% 0.38/0.58         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.38/0.58          | ((X19) = (k1_xboole_0))
% 0.38/0.58          | ~ (v1_relat_1 @ X19))),
% 0.38/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.58        | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.58  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.38/0.58  thf('38', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.58  thf('39', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (((k1_relat_1 @ k1_xboole_0)
% 0.38/0.58         = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['14', '38', '39'])).
% 0.38/0.58  thf('41', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['4', '9'])).
% 0.38/0.58  thf(t95_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.58         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]:
% 0.38/0.58         (((k7_relat_1 @ X22 @ X23) != (k1_xboole_0))
% 0.38/0.58          | (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.38/0.58          | ~ (v1_relat_1 @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      ((((sk_C_1) != (k1_xboole_0))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_C_1)
% 0.38/0.58        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      ((((sk_C_1) != (k1_xboole_0))
% 0.38/0.58        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.58  thf('47', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.38/0.58  thf('49', plain, ((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A)),
% 0.38/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.58  thf(t4_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.38/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A) = (k1_xboole_0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '52'])).
% 0.38/0.58  thf('54', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['40', '53'])).
% 0.38/0.58  thf('55', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.58         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.38/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['55', '58'])).
% 0.38/0.58  thf('60', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.58  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.58  thf('62', plain, ($false),
% 0.38/0.58      inference('simplify_reflect-', [status(thm)], ['54', '61'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
