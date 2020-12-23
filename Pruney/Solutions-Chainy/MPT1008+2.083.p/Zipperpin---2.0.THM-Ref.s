%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4FArHVWHl

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 406 expanded)
%              Number of leaves         :   35 ( 132 expanded)
%              Depth                    :   20
%              Number of atoms          :  832 (5175 expanded)
%              Number of equality atoms :   94 ( 501 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X35 @ X32 ) @ ( k2_relset_1 @ X33 @ X34 @ X35 ) ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
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

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != ( k1_tarski @ X16 ) )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('42',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','48','49','50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != ( k1_tarski @ X16 ) )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('65',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('72',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('73',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h4FArHVWHl
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 291 iterations in 0.066s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(t7_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.51  thf(t62_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.51         ( m1_subset_1 @
% 0.20/0.51           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.51           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.51            ( m1_subset_1 @
% 0.20/0.51              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.51              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t6_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X32 @ X33)
% 0.20/0.51          | ((X34) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_funct_1 @ X35)
% 0.20/0.51          | ~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.20/0.51          | (r2_hidden @ (k1_funct_1 @ X35 @ X32) @ 
% 0.20/0.51             (k2_relset_1 @ X33 @ X34 @ X35)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.20/0.51           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.20/0.51          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.51         = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.20/0.51          | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.20/0.51  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.51        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.20/0.51           (k2_relat_1 @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.51  thf(t7_ordinal1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.51        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.51             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k1_relset_1 @ X23 @ X24 @ X25) @ (k1_zfmisc_1 @ X23))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.51         = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('24', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(l45_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.20/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.20/0.51            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (((X10) = (k2_tarski @ X8 @ X9))
% 0.20/0.51          | ((X10) = (k1_tarski @ X9))
% 0.20/0.51          | ((X10) = (k1_tarski @ X8))
% 0.20/0.51          | ((X10) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X10 @ (k2_tarski @ X8 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ((X1) = (k1_tarski @ X0))
% 0.20/0.51          | ((X1) = (k1_tarski @ X0))
% 0.20/0.51          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (k2_tarski @ X0 @ X0))
% 0.20/0.51          | ((X1) = (k1_tarski @ X0))
% 0.20/0.51          | ((X1) = (k1_xboole_0))
% 0.20/0.51          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '27'])).
% 0.20/0.51  thf('29', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.51  thf(t14_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.51         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X17) != (k1_tarski @ X16))
% 0.20/0.51          | ((k2_relat_1 @ X17) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.20/0.51          | ~ (v1_funct_1 @ X17)
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.20/0.51          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ X0)
% 0.20/0.51          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('eq_res', [status(thm)], ['33'])).
% 0.20/0.51  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.20/0.51        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.51         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.20/0.51         = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.20/0.51  thf(t64_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.51         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.20/0.51          | ((X15) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf(t60_relat_1, axiom,
% 0.20/0.51    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.51     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('49', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('50', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('51', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '48', '49', '50', '51'])).
% 0.20/0.51  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (((k1_relat_1 @ X17) != (k1_tarski @ X16))
% 0.20/0.51          | ((k2_relat_1 @ X17) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.20/0.51          | ~ (v1_funct_1 @ X17)
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51          | ((k2_relat_1 @ k1_xboole_0)
% 0.20/0.51              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X12 : $i, X14 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.51          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['55', '60', '61'])).
% 0.20/0.51  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('64', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf('65', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.51          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['62', '65'])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.51        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '66'])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf('71', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.51  thf('72', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.20/0.51  thf('74', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['68', '73'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
