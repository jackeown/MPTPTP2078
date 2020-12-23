%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dc9rhfgRAF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:40 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 514 expanded)
%              Number of leaves         :   38 ( 164 expanded)
%              Depth                    :   22
%              Number of atoms          :  974 (7086 expanded)
%              Number of equality atoms :  128 ( 779 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ X31 ) @ ( k2_relset_1 @ X32 @ X33 @ X34 ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
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

thf('26',plain,(
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

thf('27',plain,(
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
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
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
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
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
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != ( k1_tarski @ X15 ) )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','51','52','53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != ( k1_tarski @ X15 ) )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_tarski @ ( k1_funct_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('63',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('73',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('75',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dc9rhfgRAF
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:18:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 316 iterations in 0.142s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.60  thf(t9_mcart_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.36/0.60                 ( ![C:$i,D:$i]:
% 0.36/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.36/0.60                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (![X28 : $i]:
% 0.36/0.60         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.36/0.60      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.36/0.60  thf(t62_funct_2, conjecture,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.60         ( m1_subset_1 @
% 0.36/0.60           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.60         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.60           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.60            ( m1_subset_1 @
% 0.36/0.60              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.60            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.60              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t6_funct_2, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.60       ( ( r2_hidden @ C @ A ) =>
% 0.36/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.60           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X31 @ X32)
% 0.36/0.60          | ((X33) = (k1_xboole_0))
% 0.36/0.60          | ~ (v1_funct_1 @ X34)
% 0.36/0.60          | ~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.36/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.36/0.60          | (r2_hidden @ (k1_funct_1 @ X34 @ X31) @ 
% 0.36/0.60             (k2_relset_1 @ X32 @ X33 @ X34)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.36/0.60           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.36/0.60          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.36/0.60          | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.36/0.60          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.60  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.36/0.60          | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.36/0.60  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.60        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.36/0.60           (k2_relat_1 @ sk_C)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['0', '11'])).
% 0.36/0.60  thf(t7_ordinal1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.36/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.36/0.60        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.60             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(cc2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.60         ((v4_relat_1 @ X22 @ X23)
% 0.36/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.36/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.60  thf('17', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.60  thf(d18_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X12 : $i, X13 : $i]:
% 0.36/0.60         (~ (v4_relat_1 @ X12 @ X13)
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.36/0.60          | ~ (v1_relat_1 @ X12))),
% 0.36/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ 
% 0.36/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(cc1_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( v1_relat_1 @ C ) ))).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.60         ((v1_relat_1 @ X19)
% 0.36/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.36/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.60  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.36/0.60  thf(t69_enumset1, axiom,
% 0.36/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.60  thf('24', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf(t70_enumset1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i]:
% 0.36/0.60         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.60  thf(t142_zfmisc_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.60     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.36/0.60       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.36/0.60            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.36/0.60            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.36/0.60            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.36/0.60            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.36/0.60            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.60         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.36/0.60          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.36/0.60          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.36/0.60          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.36/0.60          | ((X10) = (k1_tarski @ X9))
% 0.36/0.60          | ((X10) = (k1_tarski @ X8))
% 0.36/0.60          | ((X10) = (k1_tarski @ X7))
% 0.36/0.60          | ((X10) = (k1_xboole_0))
% 0.36/0.60          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k1_xboole_0))
% 0.36/0.60          | ((X2) = (k1_tarski @ X1))
% 0.36/0.60          | ((X2) = (k1_tarski @ X1))
% 0.36/0.60          | ((X2) = (k1_tarski @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i]:
% 0.36/0.60         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k1_xboole_0))
% 0.36/0.60          | ((X2) = (k1_tarski @ X1))
% 0.36/0.60          | ((X2) = (k1_tarski @ X1))
% 0.36/0.60          | ((X2) = (k1_tarski @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         (((X2) = (k2_tarski @ X1 @ X0))
% 0.36/0.60          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.36/0.60          | ((X2) = (k1_tarski @ X0))
% 0.36/0.60          | ((X2) = (k1_tarski @ X1))
% 0.36/0.60          | ((X2) = (k1_xboole_0))
% 0.36/0.60          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.36/0.60          | ((X1) = (k1_xboole_0))
% 0.36/0.60          | ((X1) = (k1_tarski @ X0))
% 0.36/0.60          | ((X1) = (k1_tarski @ X0))
% 0.36/0.60          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.36/0.60          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['24', '30'])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((X1) = (k2_tarski @ X0 @ X0))
% 0.36/0.60          | ((X1) = (k1_tarski @ X0))
% 0.36/0.60          | ((X1) = (k1_xboole_0))
% 0.36/0.60          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['23', '32'])).
% 0.36/0.60  thf('34', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.36/0.60  thf(t14_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.60       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.36/0.60         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X15 : $i, X16 : $i]:
% 0.36/0.60         (((k1_relat_1 @ X16) != (k1_tarski @ X15))
% 0.36/0.60          | ((k2_relat_1 @ X16) = (k1_tarski @ (k1_funct_1 @ X16 @ X15)))
% 0.36/0.60          | ~ (v1_funct_1 @ X16)
% 0.36/0.60          | ~ (v1_relat_1 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.36/0.60          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.36/0.60          | ~ (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_funct_1 @ X0)
% 0.36/0.60          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.36/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.60      inference('eq_res', [status(thm)], ['38'])).
% 0.36/0.60  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.36/0.60        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.36/0.60         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.36/0.60         = (k2_relat_1 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('46', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.36/0.60  thf(t64_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X14 : $i]:
% 0.36/0.60         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.36/0.60          | ((X14) = (k1_xboole_0))
% 0.36/0.60          | ~ (v1_relat_1 @ X14))),
% 0.36/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.60        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.60  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.60  thf('51', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf(t60_relat_1, axiom,
% 0.36/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.60  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.60  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('54', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf('55', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['14', '51', '52', '53', '54'])).
% 0.36/0.60  thf('56', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X15 : $i, X16 : $i]:
% 0.36/0.60         (((k1_relat_1 @ X16) != (k1_tarski @ X15))
% 0.36/0.60          | ((k2_relat_1 @ X16) = (k1_tarski @ (k1_funct_1 @ X16 @ X15)))
% 0.36/0.60          | ~ (v1_funct_1 @ X16)
% 0.36/0.60          | ~ (v1_relat_1 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.60          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.36/0.60          | ((k2_relat_1 @ k1_xboole_0)
% 0.36/0.60              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf('59', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.60          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.36/0.60          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.60  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('62', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf('63', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.36/0.60      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.60  thf('64', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.60          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['60', '63'])).
% 0.36/0.60  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.60      inference('demod', [status(thm)], ['65', '66'])).
% 0.36/0.60  thf('68', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.60          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['64', '67'])).
% 0.36/0.60  thf('69', plain,
% 0.36/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.60        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.36/0.60      inference('sup-', [status(thm)], ['55', '68'])).
% 0.36/0.60  thf('70', plain,
% 0.36/0.60      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['69'])).
% 0.36/0.60  thf('71', plain,
% 0.36/0.60      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf('73', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.60  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.60      inference('simplify', [status(thm)], ['50'])).
% 0.36/0.60  thf('75', plain,
% 0.36/0.60      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.36/0.60  thf('76', plain, ($false),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['70', '75'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
