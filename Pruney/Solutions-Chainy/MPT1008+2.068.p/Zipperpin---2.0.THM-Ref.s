%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rSKWpBNlG

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 575 expanded)
%              Number of leaves         :   40 ( 183 expanded)
%              Depth                    :   23
%              Number of atoms          : 1009 (7753 expanded)
%              Number of equality atoms :  132 ( 827 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
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

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ ( k2_relset_1 @ X35 @ X36 @ X37 ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
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

thf('30',plain,(
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

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('56',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','55','56','57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('67',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('71',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('76',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('77',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('79',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5rSKWpBNlG
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 228 iterations in 0.154s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.57  thf(t29_mcart_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.57          ( ![B:$i]:
% 0.20/0.57            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.57                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.57                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.57                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (![X30 : $i]:
% 0.20/0.57         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.20/0.57      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.57  thf(t62_funct_2, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.57         ( m1_subset_1 @
% 0.20/0.57           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.57         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.57           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.57            ( m1_subset_1 @
% 0.20/0.57              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.57            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.57              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t6_funct_2, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.57           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X34 @ X35)
% 0.20/0.57          | ((X36) = (k1_xboole_0))
% 0.20/0.57          | ~ (v1_funct_1 @ X37)
% 0.20/0.57          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.20/0.57          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.57          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ 
% 0.20/0.57             (k2_relset_1 @ X35 @ X36 @ X37)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.20/0.57           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.20/0.57          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.57          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.57          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.57         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.20/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.57         = (k2_relat_1 @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.20/0.57          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.20/0.57  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.57        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.57           (k2_relat_1 @ sk_C)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.57  thf(t7_ordinal1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.57        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.57             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(cc2_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.57         ((v4_relat_1 @ X24 @ X25)
% 0.20/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.57  thf('17', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf(t209_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X12 : $i, X13 : $i]:
% 0.20/0.57         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.20/0.57          | ~ (v4_relat_1 @ X12 @ X13)
% 0.20/0.57          | ~ (v1_relat_1 @ X12))),
% 0.20/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.57        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_C @ 
% 0.20/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(cc1_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( v1_relat_1 @ C ) ))).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((v1_relat_1 @ X21)
% 0.20/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.57  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('23', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.57  thf(t87_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X15 : $i, X16 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X15 @ X16)) @ X16)
% 0.20/0.57          | ~ (v1_relat_1 @ X15))),
% 0.20/0.57      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.57      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.57  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.20/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.57  thf(t69_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('28', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf(t70_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i]:
% 0.20/0.57         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.57  thf(t142_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.57       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.20/0.57            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.20/0.57            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.20/0.57            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.20/0.57            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.20/0.57            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.57         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.20/0.57          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.20/0.57          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.20/0.57          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.20/0.57          | ((X10) = (k1_tarski @ X9))
% 0.20/0.57          | ((X10) = (k1_tarski @ X8))
% 0.20/0.57          | ((X10) = (k1_tarski @ X7))
% 0.20/0.57          | ((X10) = (k1_xboole_0))
% 0.20/0.57          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k1_xboole_0))
% 0.20/0.57          | ((X2) = (k1_tarski @ X1))
% 0.20/0.57          | ((X2) = (k1_tarski @ X1))
% 0.20/0.57          | ((X2) = (k1_tarski @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i]:
% 0.20/0.57         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.20/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k1_xboole_0))
% 0.20/0.57          | ((X2) = (k1_tarski @ X1))
% 0.20/0.57          | ((X2) = (k1_tarski @ X1))
% 0.20/0.57          | ((X2) = (k1_tarski @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         (((X2) = (k2_tarski @ X1 @ X0))
% 0.20/0.57          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.20/0.57          | ((X2) = (k1_tarski @ X0))
% 0.20/0.57          | ((X2) = (k1_tarski @ X1))
% 0.20/0.57          | ((X2) = (k1_xboole_0))
% 0.20/0.57          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.20/0.57          | ((X1) = (k1_xboole_0))
% 0.20/0.57          | ((X1) = (k1_tarski @ X0))
% 0.20/0.57          | ((X1) = (k1_tarski @ X0))
% 0.20/0.57          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.20/0.57          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['28', '34'])).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         (((X1) = (k2_tarski @ X0 @ X0))
% 0.20/0.57          | ((X1) = (k1_tarski @ X0))
% 0.20/0.57          | ((X1) = (k1_xboole_0))
% 0.20/0.57          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '36'])).
% 0.20/0.57  thf('38', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.57  thf(t14_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.57       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.57         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X17 : $i, X18 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 0.20/0.57          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.20/0.57          | ~ (v1_funct_1 @ X18)
% 0.20/0.57          | ~ (v1_relat_1 @ X18))),
% 0.20/0.57      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.20/0.57          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X0)
% 0.20/0.57          | ~ (v1_funct_1 @ X0)
% 0.20/0.57          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.57      inference('eq_res', [status(thm)], ['42'])).
% 0.20/0.57  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('46', plain,
% 0.20/0.57      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.57        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.57  thf('47', plain,
% 0.20/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.57         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('48', plain,
% 0.20/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.57         = (k2_relat_1 @ sk_C))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf('49', plain,
% 0.20/0.57      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('50', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.20/0.57  thf(t64_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.57  thf('51', plain,
% 0.20/0.57      (![X14 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.20/0.57          | ((X14) = (k1_xboole_0))
% 0.20/0.57          | ~ (v1_relat_1 @ X14))),
% 0.20/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.57  thf('52', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.57        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.57  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('54', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.57  thf('55', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf(t60_relat_1, axiom,
% 0.20/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('56', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.57  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.57  thf('59', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '55', '56', '57', '58'])).
% 0.20/0.57  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('61', plain,
% 0.20/0.57      (![X17 : $i, X18 : $i]:
% 0.20/0.57         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 0.20/0.57          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.20/0.57          | ~ (v1_funct_1 @ X18)
% 0.20/0.57          | ~ (v1_relat_1 @ X18))),
% 0.20/0.57      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.57  thf('62', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.57          | ((k2_relat_1 @ k1_xboole_0)
% 0.20/0.57              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.57  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('64', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.57          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.57  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf('67', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.57  thf('68', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.57          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['64', '67'])).
% 0.20/0.57  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.57  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.57  thf('72', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.57          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.57      inference('demod', [status(thm)], ['68', '71'])).
% 0.20/0.57  thf('73', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.57        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['59', '72'])).
% 0.20/0.57  thf('74', plain,
% 0.20/0.57      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.57      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.57  thf('75', plain,
% 0.20/0.57      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.57  thf('76', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf('77', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.57  thf('79', plain,
% 0.20/0.57      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.57      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.20/0.57  thf('80', plain, ($false),
% 0.20/0.57      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
