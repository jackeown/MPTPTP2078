%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfeiN7xKJj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:00 EST 2020

% Result     : Theorem 47.74s
% Output     : Refutation 47.74s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 116 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (1149 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('9',plain,(
    ! [X22: $i] :
      ( ( ( k9_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ X0 @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ X0 @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k9_relat_1 @ sk_C @ X0 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['9','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X39 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['7','40'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X17: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k1_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DfeiN7xKJj
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 47.74/47.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.74/47.97  % Solved by: fo/fo7.sh
% 47.74/47.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.74/47.97  % done 28462 iterations in 47.482s
% 47.74/47.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.74/47.97  % SZS output start Refutation
% 47.74/47.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 47.74/47.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 47.74/47.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 47.74/47.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 47.74/47.97  thf(sk_A_type, type, sk_A: $i).
% 47.74/47.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 47.74/47.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 47.74/47.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 47.74/47.97  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 47.74/47.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 47.74/47.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 47.74/47.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 47.74/47.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 47.74/47.97  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 47.74/47.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 47.74/47.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 47.74/47.97  thf(sk_B_type, type, sk_B: $i > $i).
% 47.74/47.97  thf(sk_C_type, type, sk_C: $i).
% 47.74/47.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.74/47.97  thf(d10_xboole_0, axiom,
% 47.74/47.97    (![A:$i,B:$i]:
% 47.74/47.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 47.74/47.97  thf('0', plain,
% 47.74/47.97      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 47.74/47.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 47.74/47.97  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 47.74/47.97      inference('simplify', [status(thm)], ['0'])).
% 47.74/47.97  thf(t49_relset_1, conjecture,
% 47.74/47.97    (![A:$i]:
% 47.74/47.97     ( ( ~( v1_xboole_0 @ A ) ) =>
% 47.74/47.97       ( ![B:$i]:
% 47.74/47.97         ( ( ~( v1_xboole_0 @ B ) ) =>
% 47.74/47.97           ( ![C:$i]:
% 47.74/47.97             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.74/47.97               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 47.74/47.97                    ( ![D:$i]:
% 47.74/47.97                      ( ( m1_subset_1 @ D @ B ) =>
% 47.74/47.97                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 47.74/47.97  thf(zf_stmt_0, negated_conjecture,
% 47.74/47.97    (~( ![A:$i]:
% 47.74/47.97        ( ( ~( v1_xboole_0 @ A ) ) =>
% 47.74/47.97          ( ![B:$i]:
% 47.74/47.97            ( ( ~( v1_xboole_0 @ B ) ) =>
% 47.74/47.97              ( ![C:$i]:
% 47.74/47.97                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.74/47.97                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 47.74/47.97                       ( ![D:$i]:
% 47.74/47.97                         ( ( m1_subset_1 @ D @ B ) =>
% 47.74/47.97                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 47.74/47.97    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 47.74/47.97  thf('2', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf(t14_relset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i,D:$i]:
% 47.74/47.97     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 47.74/47.97       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 47.74/47.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 47.74/47.97  thf('3', plain,
% 47.74/47.97      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 47.74/47.97         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 47.74/47.97          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 47.74/47.97          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 47.74/47.97      inference('cnf', [status(esa)], [t14_relset_1])).
% 47.74/47.97  thf('4', plain,
% 47.74/47.97      (![X0 : $i]:
% 47.74/47.97         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 47.74/47.97          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 47.74/47.97      inference('sup-', [status(thm)], ['2', '3'])).
% 47.74/47.97  thf('5', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ 
% 47.74/47.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 47.74/47.97      inference('sup-', [status(thm)], ['1', '4'])).
% 47.74/47.97  thf(cc4_relset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i]:
% 47.74/47.97     ( ( v1_xboole_0 @ A ) =>
% 47.74/47.97       ( ![C:$i]:
% 47.74/47.97         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 47.74/47.97           ( v1_xboole_0 @ C ) ) ) ))).
% 47.74/47.97  thf('6', plain,
% 47.74/47.97      (![X26 : $i, X27 : $i, X28 : $i]:
% 47.74/47.97         (~ (v1_xboole_0 @ X26)
% 47.74/47.97          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 47.74/47.97          | (v1_xboole_0 @ X27))),
% 47.74/47.97      inference('cnf', [status(esa)], [cc4_relset_1])).
% 47.74/47.97  thf('7', plain,
% 47.74/47.97      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 47.74/47.97      inference('sup-', [status(thm)], ['5', '6'])).
% 47.74/47.97  thf(t146_relat_1, axiom,
% 47.74/47.97    (![A:$i]:
% 47.74/47.97     ( ( v1_relat_1 @ A ) =>
% 47.74/47.97       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 47.74/47.97  thf('8', plain,
% 47.74/47.97      (![X22 : $i]:
% 47.74/47.97         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 47.74/47.97          | ~ (v1_relat_1 @ X22))),
% 47.74/47.97      inference('cnf', [status(esa)], [t146_relat_1])).
% 47.74/47.97  thf('9', plain,
% 47.74/47.97      (![X22 : $i]:
% 47.74/47.97         (((k9_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (k2_relat_1 @ X22))
% 47.74/47.97          | ~ (v1_relat_1 @ X22))),
% 47.74/47.97      inference('cnf', [status(esa)], [t146_relat_1])).
% 47.74/47.97  thf(d1_xboole_0, axiom,
% 47.74/47.97    (![A:$i]:
% 47.74/47.97     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 47.74/47.97  thf('10', plain,
% 47.74/47.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 47.74/47.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 47.74/47.97  thf(t143_relat_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i]:
% 47.74/47.97     ( ( v1_relat_1 @ C ) =>
% 47.74/47.97       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 47.74/47.97         ( ?[D:$i]:
% 47.74/47.97           ( ( r2_hidden @ D @ B ) & 
% 47.74/47.97             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 47.74/47.97             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 47.74/47.97  thf('11', plain,
% 47.74/47.97      (![X19 : $i, X20 : $i, X21 : $i]:
% 47.74/47.97         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 47.74/47.97          | (r2_hidden @ (k4_tarski @ (sk_D @ X21 @ X19 @ X20) @ X20) @ X21)
% 47.74/47.97          | ~ (v1_relat_1 @ X21))),
% 47.74/47.97      inference('cnf', [status(esa)], [t143_relat_1])).
% 47.74/47.97  thf('12', plain,
% 47.74/47.97      (![X0 : $i, X1 : $i]:
% 47.74/47.97         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 47.74/47.97          | ~ (v1_relat_1 @ X1)
% 47.74/47.97          | (r2_hidden @ 
% 47.74/47.97             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 47.74/47.97              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 47.74/47.97             X1))),
% 47.74/47.97      inference('sup-', [status(thm)], ['10', '11'])).
% 47.74/47.97  thf('13', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf(l3_subset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i]:
% 47.74/47.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 47.74/47.97       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 47.74/47.97  thf('14', plain,
% 47.74/47.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 47.74/47.97         (~ (r2_hidden @ X12 @ X13)
% 47.74/47.97          | (r2_hidden @ X12 @ X14)
% 47.74/47.97          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 47.74/47.97      inference('cnf', [status(esa)], [l3_subset_1])).
% 47.74/47.97  thf('15', plain,
% 47.74/47.97      (![X0 : $i]:
% 47.74/47.97         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 47.74/47.97          | ~ (r2_hidden @ X0 @ sk_C))),
% 47.74/47.97      inference('sup-', [status(thm)], ['13', '14'])).
% 47.74/47.97  thf('16', plain,
% 47.74/47.97      (![X0 : $i]:
% 47.74/47.97         (~ (v1_relat_1 @ sk_C)
% 47.74/47.97          | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 47.74/47.97          | (r2_hidden @ 
% 47.74/47.97             (k4_tarski @ 
% 47.74/47.97              (sk_D @ sk_C @ X0 @ (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 47.74/47.97              (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 47.74/47.97             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('sup-', [status(thm)], ['12', '15'])).
% 47.74/47.97  thf('17', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf(cc1_relset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i]:
% 47.74/47.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.74/47.97       ( v1_relat_1 @ C ) ))).
% 47.74/47.97  thf('18', plain,
% 47.74/47.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 47.74/47.97         ((v1_relat_1 @ X23)
% 47.74/47.97          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 47.74/47.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 47.74/47.97  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 47.74/47.97      inference('sup-', [status(thm)], ['17', '18'])).
% 47.74/47.97  thf('20', plain,
% 47.74/47.97      (![X0 : $i]:
% 47.74/47.97         ((v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 47.74/47.97          | (r2_hidden @ 
% 47.74/47.97             (k4_tarski @ 
% 47.74/47.97              (sk_D @ sk_C @ X0 @ (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 47.74/47.97              (sk_B @ (k9_relat_1 @ sk_C @ X0))) @ 
% 47.74/47.97             (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('demod', [status(thm)], ['16', '19'])).
% 47.74/47.97  thf(l54_zfmisc_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i,D:$i]:
% 47.74/47.97     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 47.74/47.97       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 47.74/47.97  thf('21', plain,
% 47.74/47.97      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 47.74/47.97         ((r2_hidden @ X9 @ X10)
% 47.74/47.97          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X10)))),
% 47.74/47.97      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 47.74/47.97  thf('22', plain,
% 47.74/47.97      (![X0 : $i]:
% 47.74/47.97         ((v1_xboole_0 @ (k9_relat_1 @ sk_C @ X0))
% 47.74/47.97          | (r2_hidden @ (sk_B @ (k9_relat_1 @ sk_C @ X0)) @ sk_B_1))),
% 47.74/47.97      inference('sup-', [status(thm)], ['20', '21'])).
% 47.74/47.97  thf('23', plain,
% 47.74/47.97      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1)
% 47.74/47.97        | ~ (v1_relat_1 @ sk_C)
% 47.74/47.97        | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 47.74/47.97      inference('sup+', [status(thm)], ['9', '22'])).
% 47.74/47.97  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 47.74/47.97      inference('sup-', [status(thm)], ['17', '18'])).
% 47.74/47.97  thf('25', plain,
% 47.74/47.97      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1)
% 47.74/47.97        | (v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 47.74/47.97      inference('demod', [status(thm)], ['23', '24'])).
% 47.74/47.97  thf(t1_subset, axiom,
% 47.74/47.97    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 47.74/47.97  thf('26', plain,
% 47.74/47.97      (![X15 : $i, X16 : $i]:
% 47.74/47.97         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 47.74/47.97      inference('cnf', [status(esa)], [t1_subset])).
% 47.74/47.97  thf('27', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 47.74/47.97        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1))),
% 47.74/47.97      inference('sup-', [status(thm)], ['25', '26'])).
% 47.74/47.97  thf('28', plain,
% 47.74/47.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 47.74/47.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 47.74/47.97  thf('29', plain,
% 47.74/47.97      (![X39 : $i]:
% 47.74/47.97         (~ (r2_hidden @ X39 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 47.74/47.97          | ~ (m1_subset_1 @ X39 @ sk_B_1))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf('30', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C))
% 47.74/47.97        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C)) @ 
% 47.74/47.97             sk_B_1))),
% 47.74/47.97      inference('sup-', [status(thm)], ['28', '29'])).
% 47.74/47.97  thf('31', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf(redefinition_k2_relset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i]:
% 47.74/47.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.74/47.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 47.74/47.97  thf('32', plain,
% 47.74/47.97      (![X32 : $i, X33 : $i, X34 : $i]:
% 47.74/47.97         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 47.74/47.97          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 47.74/47.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 47.74/47.97  thf('33', plain,
% 47.74/47.97      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 47.74/47.97      inference('sup-', [status(thm)], ['31', '32'])).
% 47.74/47.97  thf('34', plain,
% 47.74/47.97      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 47.74/47.97      inference('sup-', [status(thm)], ['31', '32'])).
% 47.74/47.97  thf('35', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 47.74/47.97        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C)) @ sk_B_1))),
% 47.74/47.97      inference('demod', [status(thm)], ['30', '33', '34'])).
% 47.74/47.97  thf('36', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 47.74/47.97        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 47.74/47.97      inference('sup-', [status(thm)], ['27', '35'])).
% 47.74/47.97  thf('37', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 47.74/47.97        | ~ (v1_relat_1 @ sk_C)
% 47.74/47.97        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 47.74/47.97      inference('sup+', [status(thm)], ['8', '36'])).
% 47.74/47.97  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 47.74/47.97      inference('sup-', [status(thm)], ['17', '18'])).
% 47.74/47.97  thf('39', plain,
% 47.74/47.97      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 47.74/47.97        | (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 47.74/47.97      inference('demod', [status(thm)], ['37', '38'])).
% 47.74/47.97  thf('40', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 47.74/47.97      inference('simplify', [status(thm)], ['39'])).
% 47.74/47.97  thf('41', plain, ((v1_xboole_0 @ sk_C)),
% 47.74/47.97      inference('demod', [status(thm)], ['7', '40'])).
% 47.74/47.97  thf(fc10_relat_1, axiom,
% 47.74/47.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 47.74/47.97  thf('42', plain,
% 47.74/47.97      (![X17 : $i]:
% 47.74/47.97         ((v1_xboole_0 @ (k1_relat_1 @ X17)) | ~ (v1_xboole_0 @ X17))),
% 47.74/47.97      inference('cnf', [status(esa)], [fc10_relat_1])).
% 47.74/47.97  thf(l13_xboole_0, axiom,
% 47.74/47.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 47.74/47.97  thf('43', plain,
% 47.74/47.97      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 47.74/47.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 47.74/47.97  thf('44', plain,
% 47.74/47.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 47.74/47.97      inference('sup-', [status(thm)], ['42', '43'])).
% 47.74/47.97  thf('45', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 47.74/47.97      inference('sup-', [status(thm)], ['41', '44'])).
% 47.74/47.97  thf('46', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) != (k1_xboole_0))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf('47', plain,
% 47.74/47.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 47.74/47.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.74/47.97  thf(redefinition_k1_relset_1, axiom,
% 47.74/47.97    (![A:$i,B:$i,C:$i]:
% 47.74/47.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 47.74/47.97       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 47.74/47.97  thf('48', plain,
% 47.74/47.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 47.74/47.97         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 47.74/47.97          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 47.74/47.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 47.74/47.97  thf('49', plain,
% 47.74/47.97      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 47.74/47.97      inference('sup-', [status(thm)], ['47', '48'])).
% 47.74/47.97  thf('50', plain, (((k1_relat_1 @ sk_C) != (k1_xboole_0))),
% 47.74/47.97      inference('demod', [status(thm)], ['46', '49'])).
% 47.74/47.97  thf('51', plain, ($false),
% 47.74/47.97      inference('simplify_reflect-', [status(thm)], ['45', '50'])).
% 47.74/47.97  
% 47.74/47.97  % SZS output end Refutation
% 47.74/47.97  
% 47.74/47.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
