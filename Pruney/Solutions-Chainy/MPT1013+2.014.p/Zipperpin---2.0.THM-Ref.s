%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hZyjeKHo74

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 129 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  669 (1787 expanded)
%              Number of equality atoms :   39 ( 125 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k9_relat_1 @ X9 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t73_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ( ( ( k2_relset_1 @ A @ A @ B )
                = A )
              & ( ( k2_relset_1 @ A @ A @ C )
                = A ) )
           => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
              = A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ( ( ( k2_relset_1 @ A @ A @ B )
                  = A )
                & ( ( k2_relset_1 @ A @ A @ C )
                  = A ) )
             => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
                = A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k7_relat_1 @ X11 @ X12 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['32','37'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('47',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('54',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['16','21','47','52','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hZyjeKHo74
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:07:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 195 iterations in 0.077s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(t160_relat_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( v1_relat_1 @ B ) =>
% 0.19/0.52           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.52             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         (~ (v1_relat_1 @ X9)
% 0.19/0.52          | ((k2_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.19/0.52              = (k9_relat_1 @ X9 @ (k2_relat_1 @ X10)))
% 0.19/0.52          | ~ (v1_relat_1 @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.19/0.52  thf(t73_funct_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.52       ( ![C:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.52           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.19/0.52               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.19/0.52             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.19/0.52               ( A ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.52          ( ![C:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.19/0.52              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.19/0.52                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.19/0.52                ( ( k2_relset_1 @
% 0.19/0.52                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.19/0.52                  ( A ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_k4_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.52     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.52       ( m1_subset_1 @
% 0.19/0.52         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.19/0.52         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.19/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.19/0.52          | (m1_subset_1 @ (k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.19/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.19/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      ((m1_subset_1 @ 
% 0.19/0.52        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.52         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.19/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.52         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.19/0.52         = (k2_relat_1 @ 
% 0.19/0.52            (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (((k2_relat_1 @ (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.19/0.52         != (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['1', '8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k4_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.52     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.19/0.52       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.19/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.19/0.52          | ((k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.19/0.52              = (k5_relat_1 @ X28 @ X31)))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.52         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.19/0.52            = (k5_relat_1 @ sk_C @ X0))
% 0.19/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.19/0.52         = (k5_relat_1 @ sk_C @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['10', '13'])).
% 0.19/0.52  thf('15', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['9', '14'])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      ((((k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)) != (sk_A))
% 0.19/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '15'])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.52         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.19/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.52  thf('20', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('21', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.19/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_k1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k1_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X13))
% 0.19/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.52         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.19/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['24', '27'])).
% 0.19/0.52  thf(t3_subset, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.52  thf('30', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.19/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.52  thf(t97_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.19/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.19/0.52          | ((k7_relat_1 @ X11 @ X12) = (X11))
% 0.19/0.52          | ~ (v1_relat_1 @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (sk_B)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(cc2_relat_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.52          | (v1_relat_1 @ X3)
% 0.19/0.52          | ~ (v1_relat_1 @ X4))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf(fc6_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.52  thf('36', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.52  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.52  thf('38', plain, (((k7_relat_1 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['32', '37'])).
% 0.19/0.52  thf(t148_relat_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( v1_relat_1 @ B ) =>
% 0.19/0.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i]:
% 0.19/0.52         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.19/0.52          | ~ (v1_relat_1 @ X7))),
% 0.19/0.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 0.19/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.52         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.19/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.19/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.52  thf('44', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('45', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.52      inference('sup+', [status(thm)], ['43', '44'])).
% 0.19/0.52  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.52  thf('47', plain, (((sk_A) = (k9_relat_1 @ sk_B @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['40', '45', '46'])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('49', plain,
% 0.19/0.52      (![X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.19/0.52          | (v1_relat_1 @ X3)
% 0.19/0.52          | ~ (v1_relat_1 @ X4))),
% 0.19/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.52  thf('50', plain,
% 0.19/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.19/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.52  thf('51', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.52  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.52      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.52  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.52  thf('54', plain, (((sk_A) != (sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['16', '21', '47', '52', '53'])).
% 0.19/0.52  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
