%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8oPKfol9Wv

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:31 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 433 expanded)
%              Number of leaves         :   44 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          : 1025 (4685 expanded)
%              Number of equality atoms :  124 ( 500 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X35: $i] :
      ( ( X35 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X35 ) @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ ( k2_relset_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ ( k2_relset_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_2 = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','10','11','12'])).

thf('14',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    sk_B_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,
    ( ( ( k1_tarski @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
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

thf('31',plain,(
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

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = o_0_0_xboole_0 )
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
      = o_0_0_xboole_0 ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('48',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['45','48'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('53',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != o_0_0_xboole_0 )
      | ( X17 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('56',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_C = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('64',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ o_0_0_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','57','61','62','65'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('68',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('72',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('73',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('75',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ X0 ) ) )
      | ~ ( v1_funct_1 @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(s3_funct_1__e12_61_2__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_tarski @ k1_xboole_0 ) )
         => ( ( k1_funct_1 @ B @ C )
            = A ) )
      & ( ( k1_relat_1 @ B )
        = ( k1_tarski @ k1_xboole_0 ) )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('79',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e12_61_2__funct_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('80',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('81',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('82',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ o_0_0_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e12_61_2__funct_1])).

thf('87',plain,(
    v1_funct_1 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('89',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( o_0_0_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( o_0_0_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','91'])).

thf('93',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( o_0_0_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','92'])).

thf('94',plain,
    ( o_0_0_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('96',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('97',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('98',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('99',plain,(
    o_0_0_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ o_0_0_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8oPKfol9Wv
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:22:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 311 iterations in 0.133s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.59  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.59  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.40/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.40/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.59  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.40/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.40/0.59  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(t34_mcart_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.40/0.59          ( ![B:$i]:
% 0.40/0.59            ( ~( ( r2_hidden @ B @ A ) & 
% 0.40/0.59                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.40/0.59                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.40/0.59                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.40/0.59  thf('0', plain,
% 0.40/0.59      (![X35 : $i]:
% 0.40/0.59         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X35) @ X35))),
% 0.40/0.59      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.40/0.59  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.40/0.59  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X35 : $i]:
% 0.40/0.59         (((X35) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B_1 @ X35) @ X35))),
% 0.40/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.59  thf(t62_funct_2, conjecture,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.59         ( m1_subset_1 @
% 0.40/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.59         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.40/0.59           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.40/0.59            ( m1_subset_1 @
% 0.40/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.40/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.40/0.59            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.40/0.59              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(t6_funct_2, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.40/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.40/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.40/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X40 @ X41)
% 0.40/0.59          | ((X42) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_funct_1 @ X43)
% 0.40/0.59          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.40/0.59          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.40/0.59          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ 
% 0.40/0.59             (k2_relset_1 @ X41 @ X42 @ X43)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.40/0.59  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('6', plain,
% 0.40/0.59      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X40 @ X41)
% 0.40/0.59          | ((X42) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (v1_funct_1 @ X43)
% 0.40/0.59          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.40/0.59          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.40/0.59          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ 
% 0.40/0.59             (k2_relset_1 @ X41 @ X42 @ X43)))),
% 0.40/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.40/0.59  thf('7', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.40/0.59           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C))
% 0.40/0.59          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.40/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59          | ((sk_B_2) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.40/0.59         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.40/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.59  thf('10', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('11', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('13', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.40/0.59          | ((sk_B_2) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['7', '10', '11', '12'])).
% 0.40/0.59  thf('14', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('16', plain, (((sk_B_2) != (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.40/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['13', '16'])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      ((((k1_tarski @ sk_A) = (o_0_0_xboole_0))
% 0.40/0.59        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B_1 @ (k1_tarski @ sk_A))) @ 
% 0.40/0.59           (k2_relat_1 @ sk_C)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['2', '17'])).
% 0.40/0.59  thf(t7_ordinal1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.59  thf('19', plain,
% 0.40/0.59      (![X24 : $i, X25 : $i]:
% 0.40/0.59         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.40/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      ((((k1_tarski @ sk_A) = (o_0_0_xboole_0))
% 0.40/0.59        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.40/0.59             (k1_funct_1 @ sk_C @ (sk_B_1 @ (k1_tarski @ sk_A)))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc2_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.40/0.59         ((v4_relat_1 @ X29 @ X30)
% 0.40/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.40/0.59  thf('23', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.40/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.40/0.59  thf(d18_relat_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ B ) =>
% 0.40/0.59       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (![X15 : $i, X16 : $i]:
% 0.40/0.59         (~ (v4_relat_1 @ X15 @ X16)
% 0.40/0.59          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.40/0.59          | ~ (v1_relat_1 @ X15))),
% 0.40/0.59      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.40/0.59  thf('25', plain,
% 0.40/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      ((m1_subset_1 @ sk_C @ 
% 0.40/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(cc1_relset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.59       ( v1_relat_1 @ C ) ))).
% 0.40/0.59  thf('27', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X26)
% 0.40/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('29', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '28'])).
% 0.40/0.59  thf(t69_enumset1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.59  thf('30', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf(l45_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i,C:$i]:
% 0.40/0.59     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.40/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.40/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         (((X9) = (k2_tarski @ X7 @ X8))
% 0.40/0.59          | ((X9) = (k1_tarski @ X8))
% 0.40/0.59          | ((X9) = (k1_tarski @ X7))
% 0.40/0.59          | ((X9) = (k1_xboole_0))
% 0.40/0.59          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.40/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.40/0.59  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.40/0.59         (((X9) = (k2_tarski @ X7 @ X8))
% 0.40/0.59          | ((X9) = (k1_tarski @ X8))
% 0.40/0.59          | ((X9) = (k1_tarski @ X7))
% 0.40/0.59          | ((X9) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.40/0.59      inference('demod', [status(thm)], ['31', '32'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.40/0.59          | ((X1) = (o_0_0_xboole_0))
% 0.40/0.59          | ((X1) = (k1_tarski @ X0))
% 0.40/0.59          | ((X1) = (k1_tarski @ X0))
% 0.40/0.59          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '33'])).
% 0.40/0.59  thf('35', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((X1) = (k2_tarski @ X0 @ X0))
% 0.40/0.59          | ((X1) = (k1_tarski @ X0))
% 0.40/0.59          | ((X1) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '35'])).
% 0.40/0.59  thf('37', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.59  thf(t14_funct_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.40/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.40/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.40/0.59  thf('40', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.40/0.59          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.40/0.59          | ~ (v1_funct_1 @ X23)
% 0.40/0.59          | ~ (v1_relat_1 @ X23))),
% 0.40/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.40/0.59          | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.40/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 0.40/0.59      inference('eq_res', [status(thm)], ['41'])).
% 0.40/0.59  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.40/0.59        | ((k1_relat_1 @ sk_C) = (o_0_0_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)
% 0.40/0.59         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('47', plain,
% 0.40/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C)
% 0.40/0.59         = (k2_relat_1 @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.59  thf('49', plain, (((k1_relat_1 @ sk_C) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['45', '48'])).
% 0.40/0.59  thf(t64_relat_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( v1_relat_1 @ A ) =>
% 0.40/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.59  thf('50', plain,
% 0.40/0.59      (![X17 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.40/0.59          | ((X17) = (k1_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.59  thf('51', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('52', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('53', plain,
% 0.40/0.59      (![X17 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X17) != (o_0_0_xboole_0))
% 0.40/0.59          | ((X17) = (o_0_0_xboole_0))
% 0.40/0.59          | ~ (v1_relat_1 @ X17))),
% 0.40/0.59      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.40/0.59  thf('54', plain,
% 0.40/0.59      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.40/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.40/0.59        | ((sk_C) = (o_0_0_xboole_0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['49', '53'])).
% 0.40/0.59  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.40/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.59  thf('56', plain,
% 0.40/0.59      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ((sk_C) = (o_0_0_xboole_0)))),
% 0.40/0.59      inference('demod', [status(thm)], ['54', '55'])).
% 0.40/0.59  thf('57', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.59  thf(t60_relat_1, axiom,
% 0.40/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.59  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('59', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('60', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('61', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.40/0.59  thf('62', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.59  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.40/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.59  thf('64', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('65', plain, (![X0 : $i]: (r1_tarski @ o_0_0_xboole_0 @ X0)),
% 0.40/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.40/0.59  thf('66', plain, (((k1_tarski @ sk_A) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '57', '61', '62', '65'])).
% 0.40/0.59  thf(t70_enumset1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.59  thf('67', plain,
% 0.40/0.59      (![X2 : $i, X3 : $i]:
% 0.40/0.59         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.40/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.59  thf('68', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.59  thf('69', plain,
% 0.40/0.59      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['67', '68'])).
% 0.40/0.59  thf('70', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.59  thf('71', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('72', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('73', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.40/0.59  thf('74', plain,
% 0.40/0.59      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.40/0.59      inference('sup+', [status(thm)], ['67', '68'])).
% 0.40/0.59  thf('75', plain,
% 0.40/0.59      (![X22 : $i, X23 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.40/0.59          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.40/0.59          | ~ (v1_funct_1 @ X23)
% 0.40/0.59          | ~ (v1_relat_1 @ X23))),
% 0.40/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.40/0.59  thf('76', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         (((k1_relat_1 @ X1) != (k1_enumset1 @ X0 @ X0 @ X0))
% 0.40/0.59          | ~ (v1_relat_1 @ X1)
% 0.40/0.59          | ~ (v1_funct_1 @ X1)
% 0.40/0.59          | ((k2_relat_1 @ X1) = (k1_tarski @ (k1_funct_1 @ X1 @ X0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.40/0.59  thf('77', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((o_0_0_xboole_0) != (k1_enumset1 @ X0 @ X0 @ X0))
% 0.40/0.59          | ((k2_relat_1 @ o_0_0_xboole_0)
% 0.40/0.59              = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ X0)))
% 0.40/0.59          | ~ (v1_funct_1 @ o_0_0_xboole_0)
% 0.40/0.59          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['73', '76'])).
% 0.40/0.59  thf('78', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.40/0.59  thf(s3_funct_1__e12_61_2__funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ?[B:$i]:
% 0.40/0.59       ( ( ![C:$i]:
% 0.40/0.59           ( ( r2_hidden @ C @ ( k1_tarski @ k1_xboole_0 ) ) =>
% 0.40/0.59             ( ( k1_funct_1 @ B @ C ) = ( A ) ) ) ) & 
% 0.40/0.59         ( ( k1_relat_1 @ B ) = ( k1_tarski @ k1_xboole_0 ) ) & 
% 0.40/0.59         ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ))).
% 0.40/0.59  thf('79', plain, (![X20 : $i]: (v1_relat_1 @ (sk_B @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e12_61_2__funct_1])).
% 0.40/0.59  thf(t4_subset_1, axiom,
% 0.40/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.59  thf('80', plain,
% 0.40/0.59      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.59  thf('81', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.40/0.59  thf('82', plain,
% 0.40/0.59      (![X11 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.59      inference('demod', [status(thm)], ['80', '81'])).
% 0.40/0.59  thf(cc3_funct_1, axiom,
% 0.40/0.59    (![A:$i]:
% 0.40/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.40/0.59       ( ![B:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 0.40/0.59  thf('83', plain,
% 0.40/0.59      (![X18 : $i, X19 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.40/0.59          | (v1_funct_1 @ X18)
% 0.40/0.59          | ~ (v1_funct_1 @ X19)
% 0.40/0.59          | ~ (v1_relat_1 @ X19))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc3_funct_1])).
% 0.40/0.59  thf('84', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (v1_relat_1 @ X0)
% 0.40/0.59          | ~ (v1_funct_1 @ X0)
% 0.40/0.59          | (v1_funct_1 @ o_0_0_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['82', '83'])).
% 0.40/0.59  thf('85', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         ((v1_funct_1 @ o_0_0_xboole_0) | ~ (v1_funct_1 @ (sk_B @ X0)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['79', '84'])).
% 0.40/0.59  thf('86', plain, (![X20 : $i]: (v1_funct_1 @ (sk_B @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [s3_funct_1__e12_61_2__funct_1])).
% 0.40/0.59  thf('87', plain, ((v1_funct_1 @ o_0_0_xboole_0)),
% 0.40/0.59      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.59  thf('88', plain,
% 0.40/0.59      (![X11 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.59      inference('demod', [status(thm)], ['80', '81'])).
% 0.40/0.59  thf('89', plain,
% 0.40/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.59         ((v1_relat_1 @ X26)
% 0.40/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.40/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.59  thf('90', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.40/0.59      inference('sup-', [status(thm)], ['88', '89'])).
% 0.40/0.59  thf('91', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((o_0_0_xboole_0) != (k1_enumset1 @ X0 @ X0 @ X0))
% 0.40/0.59          | ((o_0_0_xboole_0)
% 0.40/0.59              = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ X0))))),
% 0.40/0.59      inference('demod', [status(thm)], ['77', '78', '87', '90'])).
% 0.40/0.59  thf('92', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (((o_0_0_xboole_0) != (k1_tarski @ X0))
% 0.40/0.59          | ((o_0_0_xboole_0)
% 0.40/0.59              = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ X0))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['69', '91'])).
% 0.40/0.59  thf('93', plain,
% 0.40/0.59      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.40/0.59        | ((o_0_0_xboole_0)
% 0.40/0.59            = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A))))),
% 0.40/0.59      inference('sup-', [status(thm)], ['66', '92'])).
% 0.40/0.59  thf('94', plain,
% 0.40/0.59      (((o_0_0_xboole_0) = (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 0.40/0.59      inference('simplify', [status(thm)], ['93'])).
% 0.40/0.59  thf('95', plain,
% 0.40/0.59      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.59  thf('96', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.59  thf('97', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.40/0.59  thf('98', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.40/0.59      inference('simplify', [status(thm)], ['56'])).
% 0.40/0.59  thf('99', plain,
% 0.40/0.59      (((o_0_0_xboole_0) != (k1_tarski @ (k1_funct_1 @ o_0_0_xboole_0 @ sk_A)))),
% 0.40/0.59      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.40/0.59  thf('100', plain, ($false),
% 0.40/0.59      inference('simplify_reflect-', [status(thm)], ['94', '99'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
