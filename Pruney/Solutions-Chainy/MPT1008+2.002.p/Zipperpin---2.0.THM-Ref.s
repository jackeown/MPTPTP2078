%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YSX1hpOnZc

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 310 expanded)
%              Number of leaves         :   37 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  696 (3748 expanded)
%              Number of equality atoms :   72 ( 318 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','40','41','42','43'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('45',plain,(
    ! [X18: $i] :
      ( ( v1_funct_1 @ X18 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['48','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','56'])).

thf('58',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('60',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('61',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('63',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YSX1hpOnZc
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 157 iterations in 0.049s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t7_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
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
% 0.21/0.49  thf(t6_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X32 @ X33)
% 0.21/0.49          | ((X34) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_1 @ X35)
% 0.21/0.49          | ~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.21/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.21/0.49          | (r2_hidden @ (k1_funct_1 @ X35 @ X32) @ 
% 0.21/0.49             (k2_relset_1 @ X33 @ X34 @ X35)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.21/0.49           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.21/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.49         = (k2_relat_1 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.49          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.21/0.49  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.21/0.50           (k2_relat_1 @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.50  thf(t7_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.50             (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.50         ((v4_relat_1 @ X26 @ X27)
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('17', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf(d18_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (v4_relat_1 @ X15 @ X16)
% 0.21/0.50          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.21/0.50          | ~ (v1_relat_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf(l3_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         (((X9) = (k1_tarski @ X8))
% 0.21/0.50          | ((X9) = (k1_xboole_0))
% 0.21/0.50          | ~ (r1_tarski @ X9 @ (k1_tarski @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf(t14_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.50         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 0.21/0.50          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.21/0.50          | ~ (v1_funct_1 @ X20)
% 0.21/0.50          | ~ (v1_relat_1 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.21/0.50          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.50  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.50        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.50         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.50         = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.21/0.50  thf(t64_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X17 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf(t60_relat_1, axiom,
% 0.21/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('42', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('43', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '40', '41', '42', '43'])).
% 0.21/0.50  thf(cc1_funct_1, axiom,
% 0.21/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.21/0.50  thf('45', plain, (![X18 : $i]: ((v1_funct_1 @ X18) | ~ (v1_xboole_0 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.50  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 0.21/0.50          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.21/0.50          | ~ (v1_funct_1 @ X20)
% 0.21/0.50          | ~ (v1_relat_1 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50          | ((k2_relat_1 @ k1_xboole_0)
% 0.21/0.50              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf(t4_subset_1, axiom,
% 0.21/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.50          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.50          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0)))
% 0.21/0.50          | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '53'])).
% 0.21/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.50  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0)))
% 0.21/0.50          | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('60', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf('61', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('62', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.21/0.50  thf('64', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['58', '63'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
