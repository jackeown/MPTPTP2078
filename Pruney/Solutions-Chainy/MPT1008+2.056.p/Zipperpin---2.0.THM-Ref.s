%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iZxFxzZ8DL

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 591 expanded)
%              Number of leaves         :   34 ( 186 expanded)
%              Depth                    :   23
%              Number of atoms          :  715 (7515 expanded)
%              Number of equality atoms :   78 ( 633 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != ( k1_tarski @ X13 ) )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_tarski @ ( k1_funct_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','23'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','29'])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X30 ) @ ( k2_relset_1 @ X31 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('34',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('35',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('40',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('43',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','37','40','43'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != ( k1_tarski @ X13 ) )
      | ( ( k2_relat_1 @ X14 )
        = ( k1_tarski @ ( k1_funct_1 @ X14 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('60',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('67',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('69',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iZxFxzZ8DL
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.21/0.34  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 100 iterations in 0.039s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(t29_mcart_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.49                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.49                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.49                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.49  thf(t62_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.49         ( m1_subset_1 @
% 0.21/0.49           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.49       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.49           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.49            ( m1_subset_1 @
% 0.21/0.49              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.49          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.49              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X20 @ X21)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('4', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(d18_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.49          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.21/0.49          | ~ (v1_relat_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X17)
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf(l3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((X8) = (k1_tarski @ X7))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ~ (r1_tarski @ X8 @ (k1_tarski @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf(t14_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.49         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X14) != (k1_tarski @ X13))
% 0.21/0.49          | ((k2_relat_1 @ X14) = (k1_tarski @ (k1_funct_1 @ X14 @ X13)))
% 0.21/0.49          | ~ (v1_funct_1 @ X14)
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.21/0.49          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('eq_res', [status(thm)], ['14'])).
% 0.21/0.49  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.49        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.49         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.49         = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('24', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['18', '23'])).
% 0.21/0.49  thf(t64_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X12 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 0.21/0.49          | ((X12) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '29'])).
% 0.21/0.49  thf(t6_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X30 @ X31)
% 0.21/0.49          | ((X32) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_1 @ X33)
% 0.21/0.49          | ~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.21/0.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.21/0.49          | (r2_hidden @ (k1_funct_1 @ X33 @ X30) @ 
% 0.21/0.49             (k2_relset_1 @ X31 @ X32 @ X33)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 0.21/0.49           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.49         = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('34', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('35', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf(t60_relat_1, axiom,
% 0.21/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.49  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ k1_xboole_0)
% 0.21/0.49         = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.21/0.49  thf('38', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('40', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('43', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.49          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['32', '37', '40', '43'])).
% 0.21/0.49  thf('45', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.49        | (r2_hidden @ 
% 0.21/0.49           (k1_funct_1 @ k1_xboole_0 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.21/0.49           k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '46'])).
% 0.21/0.49  thf(t7_ordinal1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.49        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.21/0.49             (k1_funct_1 @ k1_xboole_0 @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.49  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.49  thf('51', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X14) != (k1_tarski @ X13))
% 0.21/0.49          | ((k2_relat_1 @ X14) = (k1_tarski @ (k1_funct_1 @ X14 @ X13)))
% 0.21/0.49          | ~ (v1_funct_1 @ X14)
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49          | ((k2_relat_1 @ k1_xboole_0)
% 0.21/0.49              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.49          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.49          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('60', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.49          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.49        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.49  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('67', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.49  thf('68', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.21/0.49  thf('70', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['64', '69'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
