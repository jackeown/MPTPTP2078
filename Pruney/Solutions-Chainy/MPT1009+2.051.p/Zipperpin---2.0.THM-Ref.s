%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UYVZqmMPhn

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:55 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 343 expanded)
%              Number of leaves         :   40 ( 120 expanded)
%              Depth                    :   17
%              Number of atoms          :  752 (3988 expanded)
%              Number of equality atoms :   77 ( 228 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('34',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X17 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) @ X0 ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('41',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('42',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','47'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('59',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X24: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('65',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['59','60'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53','67','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UYVZqmMPhn
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:00:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 384 iterations in 0.122s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.57  thf(t64_funct_2, conjecture,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.57         ( m1_subset_1 @
% 0.36/0.57           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.57         ( r1_tarski @
% 0.36/0.57           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.36/0.57           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.57            ( m1_subset_1 @
% 0.36/0.57              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.57            ( r1_tarski @
% 0.36/0.57              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.36/0.57              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (~ (r1_tarski @ 
% 0.36/0.57          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.36/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D @ 
% 0.36/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.36/0.57          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.36/0.57           = (k9_relat_1 @ sk_D @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.36/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D @ 
% 0.36/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(cc2_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.57         ((v4_relat_1 @ X31 @ X32)
% 0.36/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.57  thf('7', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.57  thf(d18_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i]:
% 0.36/0.57         (~ (v4_relat_1 @ X15 @ X16)
% 0.36/0.57          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.36/0.57          | ~ (v1_relat_1 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.36/0.57        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_D @ 
% 0.36/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(cc1_relset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.57       ( v1_relat_1 @ C ) ))).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.57         ((v1_relat_1 @ X28)
% 0.36/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.57  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.36/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.36/0.57  thf(t69_enumset1, axiom,
% 0.36/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.57  thf('14', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf(l45_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.36/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.57         (((X9) = (k2_tarski @ X7 @ X8))
% 0.36/0.57          | ((X9) = (k1_tarski @ X8))
% 0.36/0.57          | ((X9) = (k1_tarski @ X7))
% 0.36/0.57          | ((X9) = (k1_xboole_0))
% 0.36/0.57          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.36/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_xboole_0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((X1) = (k2_tarski @ X0 @ X0))
% 0.36/0.57          | ((X1) = (k1_tarski @ X0))
% 0.36/0.57          | ((X1) = (k1_xboole_0))
% 0.36/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['13', '17'])).
% 0.36/0.57  thf('19', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.57  thf(t14_funct_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.57       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.36/0.57         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X26 : $i, X27 : $i]:
% 0.36/0.57         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.36/0.57          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.36/0.57          | ~ (v1_funct_1 @ X27)
% 0.36/0.57          | ~ (v1_relat_1 @ X27))),
% 0.36/0.57      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.36/0.57          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_funct_1 @ X0)
% 0.36/0.57          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.36/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.36/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('eq_res', [status(thm)], ['23'])).
% 0.36/0.57  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.36/0.57          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.36/0.57        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('30', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.57  thf(t209_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X21 : $i, X22 : $i]:
% 0.36/0.57         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.36/0.57          | ~ (v4_relat_1 @ X21 @ X22)
% 0.36/0.57          | ~ (v1_relat_1 @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.36/0.57        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('34', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf(t148_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.57  thf(t144_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ B ) =>
% 0.36/0.57       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i]:
% 0.36/0.57         ((r1_tarski @ (k9_relat_1 @ X17 @ X18) @ (k2_relat_1 @ X17))
% 0.36/0.57          | ~ (v1_relat_1 @ X17))),
% 0.36/0.57      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.36/0.57           (k9_relat_1 @ X1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X1)
% 0.36/0.57          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ sk_D)
% 0.36/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.36/0.57          | (r1_tarski @ 
% 0.36/0.57             (k9_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)) @ X0) @ 
% 0.36/0.57             (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.57  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('41', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('42', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_D))),
% 0.36/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.57  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '39', '40', '41', '46'])).
% 0.36/0.57  thf('48', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.36/0.57      inference('demod', [status(thm)], ['29', '47'])).
% 0.36/0.57  thf(t64_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      (![X23 : $i]:
% 0.36/0.57         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.36/0.57          | ((X23) = (k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X23))),
% 0.36/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.57        | ~ (v1_relat_1 @ sk_D)
% 0.36/0.57        | ((sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.57  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.36/0.57  thf('53', plain, (((sk_D) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.57  thf(t4_subset_1, axiom,
% 0.36/0.57    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.57         ((v4_relat_1 @ X31 @ X32)
% 0.36/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.57  thf('56', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.36/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (![X21 : $i, X22 : $i]:
% 0.36/0.57         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.36/0.57          | ~ (v4_relat_1 @ X21 @ X22)
% 0.36/0.57          | ~ (v1_relat_1 @ X21))),
% 0.36/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.57          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.57  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.57  thf('59', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.57  thf(fc3_funct_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.36/0.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.36/0.57  thf('60', plain, (![X24 : $i]: (v1_relat_1 @ (k6_relat_1 @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.57  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf('62', plain,
% 0.36/0.57      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['58', '61'])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.36/0.57          | ~ (v1_relat_1 @ X19))),
% 0.36/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['62', '63'])).
% 0.36/0.57  thf(t60_relat_1, axiom,
% 0.36/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.57  thf('65', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.57  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.36/0.57  thf('68', plain, (((sk_D) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.57  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.57  thf('70', plain, ($false),
% 0.36/0.57      inference('demod', [status(thm)], ['4', '53', '67', '68', '69'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
