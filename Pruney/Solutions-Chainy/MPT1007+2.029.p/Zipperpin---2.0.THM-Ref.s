%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TyN0WWoKYV

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:19 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 144 expanded)
%              Number of leaves         :   42 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  670 (1354 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X39 ) @ ( k2_relset_1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k11_relat_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X33 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('20',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['31','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('49',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['54','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TyN0WWoKYV
% 0.15/0.38  % Computer   : n004.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:39:54 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 119 iterations in 0.046s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.24/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.24/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.53  thf(d1_xboole_0, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.53  thf(t61_funct_2, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.24/0.53         ( m1_subset_1 @
% 0.24/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.24/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.24/0.53         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.24/0.53            ( m1_subset_1 @
% 0.24/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.24/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.24/0.53            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_C @ 
% 0.24/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t6_funct_2, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.24/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.24/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X39 @ X40)
% 0.24/0.53          | ((X41) = (k1_xboole_0))
% 0.24/0.53          | ~ (v1_funct_1 @ X42)
% 0.24/0.53          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.24/0.53          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.24/0.53          | (r2_hidden @ (k1_funct_1 @ X42 @ X39) @ 
% 0.24/0.53             (k2_relset_1 @ X40 @ X41 @ X42)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.24/0.53           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.24/0.53          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.24/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.24/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_C @ 
% 0.24/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.24/0.53         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.24/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.24/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.24/0.53         = (k2_relat_1 @ sk_C))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('9', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.24/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.24/0.53  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.24/0.53  thf(t205_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ B ) =>
% 0.24/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.24/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (![X19 : $i, X20 : $i]:
% 0.24/0.53         (((k11_relat_1 @ X19 @ X20) = (k1_xboole_0))
% 0.24/0.53          | (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.24/0.53          | ~ (v1_relat_1 @ X19))),
% 0.24/0.53      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.24/0.53  thf(t12_funct_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.24/0.53         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X23 : $i, X24 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.24/0.53          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ (k2_relat_1 @ X24))
% 0.24/0.53          | ~ (v1_funct_1 @ X24)
% 0.24/0.53          | ~ (v1_relat_1 @ X24))),
% 0.24/0.53      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ X0)
% 0.24/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.53          | ~ (v1_relat_1 @ X0)
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]:
% 0.24/0.53         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.24/0.53          | ~ (v1_funct_1 @ X0)
% 0.24/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.24/0.53          | ~ (v1_relat_1 @ X0))),
% 0.24/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_C @ 
% 0.24/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(dt_k2_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.24/0.53         ((m1_subset_1 @ (k2_relset_1 @ X33 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))
% 0.24/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.24/0.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C) @ 
% 0.24/0.53        (k1_zfmisc_1 @ sk_B_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.24/0.53         = (k2_relat_1 @ sk_C))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      ((m1_subset_1 @ (k2_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.24/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.24/0.53  thf(l3_subset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X12 @ X13)
% 0.24/0.53          | (r2_hidden @ X12 @ X14)
% 0.24/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.24/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (v1_relat_1 @ sk_C)
% 0.24/0.53          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.24/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.24/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['15', '22'])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_C @ 
% 0.24/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(cc1_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( v1_relat_1 @ C ) ))).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.24/0.53         ((v1_relat_1 @ X27)
% 0.24/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.24/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.53  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('28', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.24/0.53          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.24/0.53      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.24/0.53  thf('29', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('30', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.53  thf(d16_relat_1, axiom,
% 0.24/0.53    (![A:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ A ) =>
% 0.24/0.53       ( ![B:$i]:
% 0.24/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.24/0.53  thf('31', plain,
% 0.24/0.53      (![X15 : $i, X16 : $i]:
% 0.24/0.53         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.24/0.53          | ~ (v1_relat_1 @ X15))),
% 0.24/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.24/0.53  thf('32', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_C @ 
% 0.24/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(cc2_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.53  thf('33', plain,
% 0.24/0.53      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.24/0.53         ((v4_relat_1 @ X30 @ X31)
% 0.24/0.53          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.24/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.53  thf('34', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.24/0.53  thf(t209_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.24/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.24/0.53  thf('35', plain,
% 0.24/0.53      (![X21 : $i, X22 : $i]:
% 0.24/0.53         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.24/0.53          | ~ (v4_relat_1 @ X21 @ X22)
% 0.24/0.53          | ~ (v1_relat_1 @ X21))),
% 0.24/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.24/0.53  thf('36', plain,
% 0.24/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.53        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.24/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.53  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf('38', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['36', '37'])).
% 0.24/0.53  thf(t148_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ B ) =>
% 0.24/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.24/0.53  thf('39', plain,
% 0.24/0.53      (![X17 : $i, X18 : $i]:
% 0.24/0.53         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.24/0.53          | ~ (v1_relat_1 @ X17))),
% 0.24/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.24/0.53  thf('40', plain,
% 0.24/0.53      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.24/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.53      inference('sup+', [status(thm)], ['38', '39'])).
% 0.24/0.53  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf('42', plain,
% 0.24/0.53      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.53  thf('43', plain,
% 0.24/0.53      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.24/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.24/0.53      inference('sup+', [status(thm)], ['31', '42'])).
% 0.24/0.53  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.53  thf('45', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.24/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.53  thf('46', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.24/0.53      inference('sup+', [status(thm)], ['30', '45'])).
% 0.24/0.53  thf('47', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ k1_xboole_0)
% 0.24/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.24/0.53      inference('demod', [status(thm)], ['11', '46'])).
% 0.24/0.53  thf('48', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.24/0.53        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.24/0.53           k1_xboole_0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['0', '47'])).
% 0.24/0.53  thf(t69_enumset1, axiom,
% 0.24/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.53  thf('49', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.24/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.53  thf(fc3_xboole_0, axiom,
% 0.24/0.53    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.24/0.53  thf('50', plain,
% 0.24/0.53      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X10 @ X11))),
% 0.24/0.53      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.24/0.53  thf('51', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.24/0.53  thf('52', plain,
% 0.24/0.53      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.24/0.53        k1_xboole_0)),
% 0.24/0.53      inference('clc', [status(thm)], ['48', '51'])).
% 0.24/0.53  thf('53', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.53  thf('54', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.24/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.53  thf('55', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.53  thf('56', plain,
% 0.24/0.53      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.24/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.53  thf(t7_ordinal1, axiom,
% 0.24/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.53  thf('57', plain,
% 0.24/0.53      (![X25 : $i, X26 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.24/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.24/0.53  thf('58', plain,
% 0.24/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.24/0.53  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.53      inference('sup-', [status(thm)], ['55', '58'])).
% 0.24/0.53  thf('60', plain, ($false), inference('demod', [status(thm)], ['54', '59'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
