%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xZprFZ5ur

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 469 expanded)
%              Number of leaves         :   40 ( 155 expanded)
%              Depth                    :   21
%              Number of atoms          : 1058 (6351 expanded)
%              Number of equality atoms :  131 ( 692 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X38 @ X35 ) @ ( k2_relset_1 @ X36 @ X37 @ X38 ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X23 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

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
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
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
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != ( k1_tarski @ X16 ) )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf('48',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['47','50'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['44','45'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('57',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('58',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','56','57','58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != ( k1_tarski @ X16 ) )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['63','68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('73',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','74'])).

thf('76',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('79',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('80',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('81',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6xZprFZ5ur
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 481 iterations in 0.089s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(t9_mcart_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.54                 ( ![C:$i,D:$i]:
% 0.21/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.54                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X32 : $i]:
% 0.21/0.54         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.54  thf(t62_funct_2, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.54         ( m1_subset_1 @
% 0.21/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.54         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.54           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.54            ( m1_subset_1 @
% 0.21/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.54            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.54              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t6_funct_2, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.54       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X35 @ X36)
% 0.21/0.54          | ((X37) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_funct_1 @ X38)
% 0.21/0.54          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.21/0.54          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.21/0.54          | (r2_hidden @ (k1_funct_1 @ X38 @ X35) @ 
% 0.21/0.54             (k2_relset_1 @ X36 @ X37 @ X38)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.21/0.54           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.21/0.54          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.54         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.54         = (k2_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.54          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.21/0.54  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.21/0.54           (k2_relat_1 @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.54  thf(t7_ordinal1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.54             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.54         ((m1_subset_1 @ (k1_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X23))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.21/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.54         = (k1_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '20'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.54  thf(t71_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.54  thf(t70_enumset1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf(t69_enumset1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.54  thf('27', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.54  thf(t142_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.54     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.54       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.21/0.54            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.21/0.54            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.21/0.54            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.21/0.54            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.21/0.54            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.54         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.21/0.54          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.21/0.54          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.21/0.54          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.21/0.54          | ((X10) = (k1_tarski @ X9))
% 0.21/0.54          | ((X10) = (k1_tarski @ X8))
% 0.21/0.54          | ((X10) = (k1_tarski @ X7))
% 0.21/0.54          | ((X10) = (k1_xboole_0))
% 0.21/0.54          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.21/0.54          | ((X3) = (k1_xboole_0))
% 0.21/0.54          | ((X3) = (k1_tarski @ X2))
% 0.21/0.54          | ((X3) = (k1_tarski @ X1))
% 0.21/0.54          | ((X3) = (k1_tarski @ X0))
% 0.21/0.54          | ((X3) = (k2_tarski @ X2 @ X1))
% 0.21/0.54          | ((X3) = (k2_tarski @ X1 @ X0))
% 0.21/0.54          | ((X3) = (k2_tarski @ X2 @ X0))
% 0.21/0.54          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.21/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((X1) = (k1_xboole_0))
% 0.21/0.54          | ((X1) = (k1_tarski @ X0))
% 0.21/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.54          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '35'])).
% 0.21/0.54  thf('37', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.54  thf(t14_funct_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X17) != (k1_tarski @ X16))
% 0.21/0.54          | ((k2_relat_1 @ X17) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.21/0.54          | ~ (v1_funct_1 @ X17)
% 0.21/0.54          | ~ (v1_relat_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.21/0.54          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_funct_1 @ X0)
% 0.21/0.54          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('eq_res', [status(thm)], ['41'])).
% 0.21/0.54  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ 
% 0.21/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( v1_relat_1 @ C ) ))).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.54        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.54         = (k2_relat_1 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['47', '50'])).
% 0.21/0.54  thf(t64_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (![X15 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.21/0.54          | ((X15) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.54        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.54  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf(t60_relat_1, axiom,
% 0.21/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('57', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('58', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['14', '56', '57', '58', '59'])).
% 0.21/0.54  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X17) != (k1_tarski @ X16))
% 0.21/0.54          | ((k2_relat_1 @ X17) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.21/0.54          | ~ (v1_funct_1 @ X17)
% 0.21/0.54          | ~ (v1_relat_1 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.54          | ((k2_relat_1 @ k1_xboole_0)
% 0.21/0.54              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (![X12 : $i, X14 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         ((v1_relat_1 @ X20)
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.54  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.54  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['63', '68', '69'])).
% 0.21/0.54  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf('73', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.54      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['60', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf('79', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.54  thf('80', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.21/0.54  thf('82', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['76', '81'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
