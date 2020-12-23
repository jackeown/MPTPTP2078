%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cn4LKgbwti

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:11 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 179 expanded)
%              Number of leaves         :   36 (  69 expanded)
%              Depth                    :   17
%              Number of atoms          :  564 (1672 expanded)
%              Number of equality atoms :   25 (  68 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','13','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X15 ) ) )
      | ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['15','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','36'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['15','32'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X11: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k2_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cn4LKgbwti
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:24:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 120 iterations in 0.048s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(dt_k2_subset_1, axiom,
% 0.19/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.49  thf('1', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.49  thf('2', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf(t50_relset_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.49               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49                    ( ![D:$i]:
% 0.19/0.49                      ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.49                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.49                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49                       ( ![D:$i]:
% 0.19/0.49                         ( ( m1_subset_1 @ D @ B ) =>
% 0.19/0.49                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t13_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.19/0.49       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.19/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.19/0.49          | (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.19/0.49          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.19/0.49      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.19/0.49          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf(d1_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X36 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X36 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C))
% 0.19/0.49          | ~ (m1_subset_1 @ X36 @ sk_B_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (((v1_xboole_0 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_B @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C)) @ 
% 0.19/0.49             sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.49         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.19/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '13', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.49         ((v4_relat_1 @ X20 @ X21)
% 0.19/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('19', plain, ((v4_relat_1 @ sk_C @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf(t209_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.49       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.19/0.49          | ~ (v4_relat_1 @ X12 @ X13)
% 0.19/0.49          | ~ (v1_relat_1 @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( v1_relat_1 @ C ) ))).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         ((v1_relat_1 @ X17)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.49  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['21', '24'])).
% 0.19/0.49  thf(t86_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.19/0.49         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X14 @ (k1_relat_1 @ (k7_relat_1 @ X16 @ X15)))
% 0.19/0.49          | (r2_hidden @ X14 @ X15)
% 0.19/0.49          | ~ (v1_relat_1 @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.19/0.49          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.49          | (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)) | (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.19/0.49        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '29'])).
% 0.19/0.49  thf(t1_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.19/0.49        | (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['15', '32'])).
% 0.19/0.49  thf(l13_xboole_0, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('35', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))
% 0.19/0.49          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['7', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '36'])).
% 0.19/0.49  thf(cc3_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49           ( v1_xboole_0 @ C ) ) ) ))).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 0.19/0.49          | (v1_xboole_0 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.19/0.49  thf('39', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('40', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['15', '32'])).
% 0.19/0.49  thf(fc11_relat_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X11 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X11 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ X0)
% 0.19/0.49          | ((k2_relat_1 @ (k2_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X11 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ k1_xboole_0)
% 0.19/0.49          | ~ (v1_xboole_0 @ X0)
% 0.19/0.49          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['45', '46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X11 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X11)) | ~ (v1_xboole_0 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.49      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.49  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '49'])).
% 0.19/0.49  thf('51', plain, ((v1_xboole_0 @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['39', '50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('53', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf('54', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.49         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.19/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.49  thf('58', plain, (((k2_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['54', '57'])).
% 0.19/0.49  thf('59', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
