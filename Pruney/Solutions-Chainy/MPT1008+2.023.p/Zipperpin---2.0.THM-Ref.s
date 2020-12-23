%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XvFQCjyrVm

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 573 expanded)
%              Number of leaves         :   38 ( 181 expanded)
%              Depth                    :   21
%              Number of atoms          :  981 (7988 expanded)
%              Number of equality atoms :  124 ( 874 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X17
        = ( k1_enumset1 @ X14 @ X15 @ X16 ) )
      | ( X17
        = ( k2_tarski @ X14 @ X16 ) )
      | ( X17
        = ( k2_tarski @ X15 @ X16 ) )
      | ( X17
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17
        = ( k1_tarski @ X15 ) )
      | ( X17
        = ( k1_tarski @ X14 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
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
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
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
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C_1 )
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
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_C_1 = k1_xboole_0 ),
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
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['14','51','52','53','54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('67',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','69'])).

thf('71',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('73',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('74',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('75',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('76',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XvFQCjyrVm
% 0.17/0.36  % Computer   : n024.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 18:21:51 EST 2020
% 0.17/0.36  % CPUTime    : 
% 0.17/0.36  % Running portfolio for 600 s
% 0.17/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.36  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 426 iterations in 0.144s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.42/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf(t62_funct_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.62         ( m1_subset_1 @
% 0.42/0.62           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.42/0.62           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.62            ( m1_subset_1 @
% 0.42/0.62              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.42/0.62              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t6_funct_2, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62       ( ( r2_hidden @ C @ A ) =>
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X35 @ X36)
% 0.42/0.62          | ((X37) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_funct_1 @ X38)
% 0.42/0.62          | ~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.42/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.42/0.62          | (r2_hidden @ (k1_funct_1 @ X38 @ X35) @ 
% 0.42/0.62             (k2_relset_1 @ X36 @ X37 @ X38)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.42/0.62           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 0.42/0.62          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.62          | ((sk_B) = (k1_xboole_0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.42/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.42/0.62         = (k2_relat_1 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.42/0.62          | ((sk_B) = (k1_xboole_0))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.42/0.62  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.42/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.42/0.62          | (r2_hidden @ 
% 0.42/0.62             (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.42/0.62             (k2_relat_1 @ sk_C_1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '11'])).
% 0.42/0.62  thf(t7_ordinal1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X24 : $i, X25 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.42/0.62          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.42/0.62               (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.42/0.62         ((v4_relat_1 @ X29 @ X30)
% 0.42/0.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('17', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.62  thf(d18_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X19 : $i, X20 : $i]:
% 0.42/0.62         (~ (v4_relat_1 @ X19 @ X20)
% 0.42/0.62          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X19))),
% 0.42/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_C_1)
% 0.42/0.62        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C_1 @ 
% 0.42/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( v1_relat_1 @ C ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.42/0.62         ((v1_relat_1 @ X26)
% 0.42/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.62  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['19', '22'])).
% 0.42/0.62  thf(t69_enumset1, axiom,
% 0.42/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.62  thf('24', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf(t70_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf(t142_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.62       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.42/0.62            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.42/0.62            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.42/0.62            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.42/0.62            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.42/0.62            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (((X17) = (k1_enumset1 @ X14 @ X15 @ X16))
% 0.42/0.62          | ((X17) = (k2_tarski @ X14 @ X16))
% 0.42/0.62          | ((X17) = (k2_tarski @ X15 @ X16))
% 0.42/0.62          | ((X17) = (k2_tarski @ X14 @ X15))
% 0.42/0.62          | ((X17) = (k1_tarski @ X16))
% 0.42/0.62          | ((X17) = (k1_tarski @ X15))
% 0.42/0.62          | ((X17) = (k1_tarski @ X14))
% 0.42/0.62          | ((X17) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_tarski @ X17 @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k1_xboole_0))
% 0.42/0.62          | ((X2) = (k1_tarski @ X1))
% 0.42/0.62          | ((X2) = (k1_tarski @ X1))
% 0.42/0.62          | ((X2) = (k1_tarski @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      (![X9 : $i, X10 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k1_xboole_0))
% 0.42/0.62          | ((X2) = (k1_tarski @ X1))
% 0.42/0.62          | ((X2) = (k1_tarski @ X1))
% 0.42/0.62          | ((X2) = (k1_tarski @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((X2) = (k2_tarski @ X1 @ X0))
% 0.42/0.62          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.42/0.62          | ((X2) = (k1_tarski @ X0))
% 0.42/0.62          | ((X2) = (k1_tarski @ X1))
% 0.42/0.62          | ((X2) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.42/0.62          | ((X1) = (k1_xboole_0))
% 0.42/0.62          | ((X1) = (k1_tarski @ X0))
% 0.42/0.62          | ((X1) = (k1_tarski @ X0))
% 0.42/0.62          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.42/0.62          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X1) = (k2_tarski @ X0 @ X0))
% 0.42/0.62          | ((X1) = (k1_tarski @ X0))
% 0.42/0.62          | ((X1) = (k1_xboole_0))
% 0.42/0.62          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ sk_A)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['23', '32'])).
% 0.42/0.62  thf('34', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['35'])).
% 0.42/0.62  thf(t14_funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.42/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.42/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.42/0.62          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.42/0.62          | ~ (v1_funct_1 @ X23)
% 0.42/0.62          | ~ (v1_relat_1 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.42/0.62          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X0)
% 0.42/0.62          | ~ (v1_funct_1 @ X0)
% 0.42/0.62          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('eq_res', [status(thm)], ['38'])).
% 0.42/0.62  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.42/0.62        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.42/0.62         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.42/0.62         = (k2_relat_1 @ sk_C_1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.42/0.62  thf(t64_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X21 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.42/0.62          | ((X21) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.62        | ((sk_C_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.42/0.62  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.62  thf('51', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf(t60_relat_1, axiom,
% 0.42/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.42/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.42/0.62  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.62  thf('53', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('54', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('55', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.42/0.62      inference('demod', [status(thm)], ['14', '51', '52', '53', '54'])).
% 0.42/0.62  thf('56', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf(d10_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X4 : $i, X6 : $i]:
% 0.42/0.62         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.42/0.62  thf('59', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['55', '58'])).
% 0.42/0.62  thf('60', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.42/0.62          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.42/0.62          | ~ (v1_funct_1 @ X23)
% 0.42/0.62          | ~ (v1_relat_1 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ sk_C_1)
% 0.42/0.62          | ~ (v1_funct_1 @ sk_C_1)
% 0.42/0.62          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('63', plain, ((v1_relat_1 @ sk_C_1)),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.42/0.62          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.42/0.62  thf('66', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf('67', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.62  thf('68', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.42/0.62          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.42/0.62  thf('70', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['59', '69'])).
% 0.42/0.62  thf('71', plain,
% 0.42/0.62      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['70'])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('73', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf('74', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.62  thf('75', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.42/0.62      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.42/0.62  thf('77', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['71', '76'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
