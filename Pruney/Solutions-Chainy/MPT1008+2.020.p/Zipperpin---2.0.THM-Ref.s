%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jfJhMBjFmL

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:33 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 185 expanded)
%              Number of leaves         :   36 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  645 (2201 expanded)
%              Number of equality atoms :   58 ( 176 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

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

thf('4',plain,(
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

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ ( k2_relset_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v4_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
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
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['25','49','50','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jfJhMBjFmL
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:36:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.44/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.61  % Solved by: fo/fo7.sh
% 0.44/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.61  % done 500 iterations in 0.169s
% 0.44/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.61  % SZS output start Refutation
% 0.44/0.61  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.61  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.61  thf(t69_enumset1, axiom,
% 0.44/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.61  thf('0', plain, (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.44/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.61  thf(d2_tarski, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.44/0.61       ( ![D:$i]:
% 0.44/0.61         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.44/0.61  thf('1', plain,
% 0.44/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.61         (((X5) != (X4))
% 0.44/0.61          | (r2_hidden @ X5 @ X6)
% 0.44/0.61          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.44/0.61      inference('cnf', [status(esa)], [d2_tarski])).
% 0.44/0.61  thf('2', plain,
% 0.44/0.61      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.44/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.44/0.61  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.61      inference('sup+', [status(thm)], ['0', '2'])).
% 0.44/0.61  thf(t62_funct_2, conjecture,
% 0.44/0.61    (![A:$i,B:$i,C:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.61         ( m1_subset_1 @
% 0.44/0.61           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.61       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.61         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.61           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.61            ( m1_subset_1 @
% 0.44/0.61              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.61          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.61            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.61              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.44/0.61    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.44/0.61  thf('4', plain,
% 0.44/0.61      ((m1_subset_1 @ sk_C @ 
% 0.44/0.61        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf(t6_funct_2, axiom,
% 0.44/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.61       ( ( r2_hidden @ C @ A ) =>
% 0.44/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.44/0.61           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.44/0.61  thf('5', plain,
% 0.44/0.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.44/0.61         (~ (r2_hidden @ X40 @ X41)
% 0.44/0.61          | ((X42) = (k1_xboole_0))
% 0.44/0.61          | ~ (v1_funct_1 @ X43)
% 0.44/0.61          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.44/0.61          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.44/0.61          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ 
% 0.44/0.61             (k2_relset_1 @ X41 @ X42 @ X43)))),
% 0.44/0.61      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.44/0.61  thf('6', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.44/0.61           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.44/0.61          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.44/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.44/0.62          | ((sk_B_1) = (k1_xboole_0))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.62         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 0.44/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.44/0.62         = (k2_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('10', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.44/0.62          | ((sk_B_1) = (k1_xboole_0))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 0.44/0.62  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.44/0.62          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['3', '14'])).
% 0.44/0.62  thf(t63_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.44/0.62       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X19 : $i, X20 : $i]:
% 0.44/0.62         ((m1_subset_1 @ (k1_tarski @ X19) @ (k1_zfmisc_1 @ X20))
% 0.44/0.62          | ~ (r2_hidden @ X19 @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      ((m1_subset_1 @ (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_relat_1 @ sk_C)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.62  thf(t3_subset, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i]:
% 0.44/0.62         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.44/0.62        (k2_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf(d10_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X0 : $i, X2 : $i]:
% 0.44/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.44/0.62           (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.44/0.62        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.44/0.62         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.44/0.62         = (k2_relat_1 @ sk_C))),
% 0.44/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.44/0.62          (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['21', '24'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc2_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.62         ((v4_relat_1 @ X32 @ X33)
% 0.44/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.62  thf('28', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.62  thf(d18_relat_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ B ) =>
% 0.44/0.62       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X24 : $i, X25 : $i]:
% 0.44/0.62         (~ (v4_relat_1 @ X24 @ X25)
% 0.44/0.62          | (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.44/0.62          | ~ (v1_relat_1 @ X24))),
% 0.44/0.62      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.44/0.62        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.62  thf('31', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C @ 
% 0.44/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(cc1_relset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.62       ( v1_relat_1 @ C ) ))).
% 0.44/0.62  thf('32', plain,
% 0.44/0.62      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.44/0.62         ((v1_relat_1 @ X29)
% 0.44/0.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.44/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.62  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('34', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['30', '33'])).
% 0.44/0.62  thf(l3_zfmisc_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.44/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         (((X17) = (k1_tarski @ X16))
% 0.44/0.62          | ((X17) = (k1_xboole_0))
% 0.44/0.62          | ~ (r1_tarski @ X17 @ (k1_tarski @ X16)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.44/0.62        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.44/0.62  thf(t14_funct_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.62       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.44/0.62         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X27 : $i, X28 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.44/0.62          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.44/0.62          | ~ (v1_funct_1 @ X28)
% 0.44/0.62          | ~ (v1_relat_1 @ X28))),
% 0.44/0.62      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.44/0.62          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.44/0.62          | ~ (v1_relat_1 @ X0)
% 0.44/0.62          | ~ (v1_funct_1 @ X0)
% 0.44/0.62          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.44/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.44/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.44/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.44/0.62        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.44/0.62      inference('eq_res', [status(thm)], ['38'])).
% 0.44/0.62  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.44/0.62        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.62  thf('44', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.44/0.62  thf(t64_relat_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( v1_relat_1 @ A ) =>
% 0.44/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (![X26 : $i]:
% 0.44/0.62         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 0.44/0.62          | ((X26) = (k1_xboole_0))
% 0.44/0.62          | ~ (v1_relat_1 @ X26))),
% 0.44/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.44/0.62        | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.44/0.62  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.44/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.44/0.62  thf('49', plain, (((sk_C) = (k1_xboole_0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.44/0.62  thf(t60_relat_1, axiom,
% 0.44/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.44/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.44/0.62  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.44/0.62  thf('51', plain, (((sk_C) = (k1_xboole_0))),
% 0.44/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.44/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.62  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.44/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.62  thf('53', plain, ($false),
% 0.44/0.62      inference('demod', [status(thm)], ['25', '49', '50', '51', '52'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
