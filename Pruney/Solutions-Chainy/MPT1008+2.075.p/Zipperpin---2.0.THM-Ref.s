%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIKsojtlFe

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 145 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  623 (1786 expanded)
%              Number of equality atoms :   49 ( 131 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k2_tarski @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X1: $i,X4: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X4 @ X1 ) ) ),
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

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ ( k2_relset_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k11_relat_1 @ X18 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k7_relset_1 @ X31 @ X32 @ X33 @ X31 )
        = ( k2_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('29',plain,
    ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('34',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('41',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','39','40','41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['17','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIKsojtlFe
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 126 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('0', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf(d2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X2) != (X1))
% 0.21/0.50          | (r2_hidden @ X2 @ X3)
% 0.21/0.50          | ((X3) != (k2_tarski @ X4 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X1 : $i, X4 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X4 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.50  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['0', '2'])).
% 0.21/0.50  thf(t62_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.50           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.50            ( m1_subset_1 @
% 0.21/0.50              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.50            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.50              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t6_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X34 @ X35)
% 0.21/0.50          | ((X36) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_funct_1 @ X37)
% 0.21/0.50          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.21/0.50          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.21/0.50          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ 
% 0.21/0.50             (k2_relset_1 @ X35 @ X36 @ X37)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.21/0.50           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.50          | ((sk_B) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.50          | ((sk_B) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 0.21/0.50  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '14'])).
% 0.21/0.50  thf(t7_ordinal1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_funct_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf(t205_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.50         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (((k11_relat_1 @ X15 @ X16) = (k1_xboole_0))
% 0.21/0.50          | (r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.21/0.50          | ~ (v1_relat_1 @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.21/0.50  thf(t117_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.50         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.50          | ((k11_relat_1 @ X18 @ X17) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 0.21/0.50          | ~ (v1_funct_1 @ X18)
% 0.21/0.50          | ~ (v1_relat_1 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k11_relat_1 @ X0 @ X1) = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.21/0.50         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C) != (k11_relat_1 @ sk_C @ sk_A))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.50  thf(d16_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.21/0.50          | ~ (v1_relat_1 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t38_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.50         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.50         (((k7_relset_1 @ X31 @ X32 @ X33 @ X31)
% 0.21/0.50            = (k2_relset_1 @ X31 @ X32 @ X33))
% 0.21/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ (k1_tarski @ sk_A))
% 0.21/0.50         = (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.50          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C @ X0)
% 0.21/0.50           = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['26', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X21)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '38'])).
% 0.21/0.50  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('41', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '38'])).
% 0.21/0.50  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.50        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '39', '40', '41', '42'])).
% 0.21/0.50  thf('44', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('46', plain, ($false),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '44', '45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
