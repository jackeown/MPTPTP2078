%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bq2cLGBaEq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 186 expanded)
%              Number of leaves         :   43 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  622 (2108 expanded)
%              Number of equality atoms :   46 ( 150 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

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
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k11_relat_1 @ X12 @ X13 )
        = ( k9_relat_1 @ X12 @ ( k1_tarski @ X13 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('24',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('36',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('38',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_tarski @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k11_relat_1 @ X20 @ X19 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bq2cLGBaEq
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 99 iterations in 0.047s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(t146_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.20/0.49          | ~ (v1_relat_1 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.49  thf(t62_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.49         ( m1_subset_1 @
% 0.20/0.49           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.49       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.49           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.49            ( m1_subset_1 @
% 0.20/0.49              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.49          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.49              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.49  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_1, axiom,
% 0.20/0.49    (![C:$i,B:$i,A:$i]:
% 0.20/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.20/0.49          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.20/0.49          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.49        | ((k1_tarski @ sk_A)
% 0.20/0.49            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(zf_stmt_2, axiom,
% 0.20/0.49    (![B:$i,A:$i]:
% 0.20/0.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i]:
% 0.20/0.49         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.49  thf(zf_stmt_5, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.49         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.20/0.49          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.20/0.49          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.49        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0))
% 0.20/0.49        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.49  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.20/0.49  thf(d16_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X12 @ X13) = (k9_relat_1 @ X12 @ (k1_tarski @ X13)))
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C)))
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup+', [status(thm)], ['0', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.20/0.50          | (v1_relat_1 @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.50        | (v1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('24', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.20/0.50         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.50         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X21 @ X22)
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('32', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(d18_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (v4_relat_1 @ X14 @ X15)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.20/0.50          | ~ (v1_relat_1 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.50        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('36', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.20/0.50  thf('38', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('40', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(t38_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k2_tarski @ X6 @ X8) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '42'])).
% 0.20/0.50  thf('44', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.50  thf(t117_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.20/0.50          | ((k11_relat_1 @ X20 @ X19) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.20/0.50          | ~ (v1_funct_1 @ X20)
% 0.20/0.50          | ~ (v1_relat_1 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.50        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.20/0.50            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((k11_relat_1 @ sk_C @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.50  thf('50', plain, (((k2_relat_1 @ sk_C) != (k11_relat_1 @ sk_C @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '49'])).
% 0.20/0.50  thf('51', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['24', '50'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
