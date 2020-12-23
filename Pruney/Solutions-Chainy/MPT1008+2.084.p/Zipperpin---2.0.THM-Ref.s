%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bk2VUszMaS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:43 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 218 expanded)
%              Number of leaves         :   38 (  80 expanded)
%              Depth                    :   17
%              Number of atoms          :  966 (2789 expanded)
%              Number of equality atoms :  110 ( 292 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X11
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( r1_tarski @ ( k1_tarski @ X7 ) @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_tarski @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

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

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ( X38 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X39 @ X36 ) @ ( k2_relset_1 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('15',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','15','16','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X27 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != ( k1_tarski @ X20 ) )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','55'])).

thf('57',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['23','65','66','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Bk2VUszMaS
% 0.15/0.36  % Computer   : n012.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:59:07 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 599 iterations in 0.217s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('0', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t70_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf(t142_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.68       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.45/0.68            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.45/0.68            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.45/0.68         ((r1_tarski @ X11 @ (k1_enumset1 @ X7 @ X8 @ X9))
% 0.45/0.68          | ((X11) != (k1_tarski @ X7)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.68         (r1_tarski @ (k1_tarski @ X7) @ (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.45/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.68  thf('4', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(t38_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.68         ((r2_hidden @ X12 @ X13)
% 0.45/0.68          | ~ (r1_tarski @ (k2_tarski @ X12 @ X14) @ X13))),
% 0.45/0.68      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['3', '6'])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['1', '7'])).
% 0.45/0.68  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['0', '8'])).
% 0.45/0.68  thf(t62_funct_2, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.68         ( m1_subset_1 @
% 0.45/0.68           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.68         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.68           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.68            ( m1_subset_1 @
% 0.45/0.68              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.68          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.68            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.68              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t6_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( r2_hidden @ C @ A ) =>
% 0.45/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X36 @ X37)
% 0.45/0.68          | ((X38) = (k1_xboole_0))
% 0.45/0.68          | ~ (v1_funct_1 @ X39)
% 0.45/0.68          | ~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.45/0.68          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.45/0.68          | (r2_hidden @ (k1_funct_1 @ X39 @ X36) @ 
% 0.45/0.68             (k2_relset_1 @ X37 @ X38 @ X39)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.45/0.68           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))
% 0.45/0.68          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)
% 0.45/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.45/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '15', '16', '17'])).
% 0.45/0.68  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.45/0.68          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['9', '20'])).
% 0.45/0.68  thf(t7_ordinal1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.45/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_funct_1 @ sk_C @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.68  thf('25', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (k1_relset_1 @ X27 @ X28 @ X29) @ (k1_zfmisc_1 @ X27))
% 0.45/0.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.68  thf('27', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.68         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.45/0.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['26', '29'])).
% 0.45/0.68  thf(t3_subset, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.68  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf(t71_enumset1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.68  thf('39', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.68         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.45/0.68          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.45/0.68          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.45/0.68          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.45/0.68          | ((X10) = (k1_tarski @ X9))
% 0.45/0.68          | ((X10) = (k1_tarski @ X8))
% 0.45/0.68          | ((X10) = (k1_tarski @ X7))
% 0.45/0.68          | ((X10) = (k1_xboole_0))
% 0.45/0.68          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.45/0.68          | ((X3) = (k1_xboole_0))
% 0.45/0.68          | ((X3) = (k1_tarski @ X2))
% 0.45/0.68          | ((X3) = (k1_tarski @ X1))
% 0.45/0.68          | ((X3) = (k1_tarski @ X0))
% 0.45/0.68          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.45/0.68          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.45/0.68          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.45/0.68          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['37', '40'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]:
% 0.45/0.68         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((X1) = (k1_xboole_0))
% 0.45/0.68          | ((X1) = (k1_tarski @ X0))
% 0.45/0.68          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.45/0.68          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['32', '44'])).
% 0.45/0.68  thf('46', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.45/0.68  thf(t14_funct_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.68       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.45/0.68         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('49', plain,
% 0.45/0.68      (![X20 : $i, X21 : $i]:
% 0.45/0.68         (((k1_relat_1 @ X21) != (k1_tarski @ X20))
% 0.45/0.68          | ((k2_relat_1 @ X21) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.45/0.68          | ~ (v1_funct_1 @ X21)
% 0.45/0.68          | ~ (v1_relat_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.45/0.68  thf('50', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.45/0.68          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('eq_res', [status(thm)], ['50'])).
% 0.45/0.68  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc1_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( v1_relat_1 @ C ) ))).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         ((v1_relat_1 @ X24)
% 0.45/0.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.68  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '52', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.45/0.68         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('60', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.45/0.68  thf(t64_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.68         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      (![X19 : $i]:
% 0.45/0.68         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.45/0.68          | ((X19) = (k1_xboole_0))
% 0.45/0.68          | ~ (v1_relat_1 @ X19))),
% 0.45/0.68      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.68  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.68  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['64'])).
% 0.45/0.68  thf(t60_relat_1, axiom,
% 0.45/0.68    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.68     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.68  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.68  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['64'])).
% 0.45/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.68  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.68  thf('69', plain, ($false),
% 0.45/0.68      inference('demod', [status(thm)], ['23', '65', '66', '67', '68'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
