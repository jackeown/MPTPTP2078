%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.71grWCia5n

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:18 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 166 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  605 (1734 expanded)
%              Number of equality atoms :   37 ( 103 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_2 )
        = sk_B )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( X30
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X30 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X29 @ X26 ) @ ( k2_relset_1 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('42',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( ( k2_relat_1 @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf('54',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['31','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.71grWCia5n
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 17:38:23 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 346 iterations in 0.282s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.75  thf(sk_E_type, type, sk_E: $i > $i).
% 0.54/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.75  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.54/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.54/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.75  thf(d3_tarski, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf(d10_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('2', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.54/0.75      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.75  thf(t3_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X9 : $i, X11 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.75  thf(t5_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.54/0.75          ( v1_xboole_0 @ C ) ) ))).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X12 @ X13)
% 0.54/0.75          | ~ (v1_xboole_0 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_subset])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '6'])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['0', '6'])).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X6 : $i, X8 : $i]:
% 0.54/0.75         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.54/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['7', '10'])).
% 0.54/0.75  thf(t16_funct_2, conjecture,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75       ( ( ![D:$i]:
% 0.54/0.75           ( ~( ( r2_hidden @ D @ B ) & 
% 0.54/0.75                ( ![E:$i]:
% 0.54/0.75                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.54/0.75                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.54/0.75         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.75          ( ( ![D:$i]:
% 0.54/0.75              ( ~( ( r2_hidden @ D @ B ) & 
% 0.54/0.75                   ( ![E:$i]:
% 0.54/0.75                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.54/0.75                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.54/0.75            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.75         ((v5_relat_1 @ X20 @ X22)
% 0.54/0.75          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('14', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.75  thf(d19_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i]:
% 0.54/0.75         (~ (v5_relat_1 @ X15 @ X16)
% 0.54/0.75          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.54/0.75          | ~ (v1_relat_1 @ X15))),
% 0.54/0.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc1_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( v1_relat_1 @ C ) ))).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         ((v1_relat_1 @ X17)
% 0.54/0.75          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.54/0.75  thf('19', plain, ((v1_relat_1 @ sk_C_2)),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.75  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '19'])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (v1_xboole_0 @ X0)
% 0.54/0.75          | ~ (v1_xboole_0 @ sk_B)
% 0.54/0.75          | ~ (v1_xboole_0 @ X0)
% 0.54/0.75          | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['11', '22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k2_relat_1 @ sk_C_2) = (sk_B))
% 0.54/0.75          | ~ (v1_xboole_0 @ sk_B)
% 0.54/0.75          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['23'])).
% 0.54/0.75  thf('25', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.75         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.54/0.75          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf('29', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.54/0.75      inference('demod', [status(thm)], ['25', '28'])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['24', '29'])).
% 0.54/0.75  thf('31', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.54/0.75      inference('condensation', [status(thm)], ['30'])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X30 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X30 @ sk_B)
% 0.54/0.75          | ((X30) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X30))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('34', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((r1_tarski @ sk_B @ X0)
% 0.54/0.75          | ((sk_C @ X0 @ sk_B)
% 0.54/0.75              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.76      (![X30 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X30 @ sk_B) | (r2_hidden @ (sk_E @ X30) @ sk_A))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ sk_B @ X0)
% 0.54/0.76          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(t6_funct_2, axiom,
% 0.54/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.54/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.76       ( ( r2_hidden @ C @ A ) =>
% 0.54/0.76         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.54/0.76           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.76         (~ (r2_hidden @ X26 @ X27)
% 0.54/0.76          | ((X28) = (k1_xboole_0))
% 0.54/0.76          | ~ (v1_funct_1 @ X29)
% 0.54/0.76          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.54/0.76          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.54/0.76          | (r2_hidden @ (k1_funct_1 @ X29 @ X26) @ 
% 0.54/0.76             (k2_relset_1 @ X27 @ X28 @ X29)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ 
% 0.54/0.76           (k2_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 0.54/0.76          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.54/0.76          | ~ (v1_funct_1 @ sk_C_2)
% 0.54/0.76          | ((sk_B) = (k1_xboole_0))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.54/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.54/0.76  thf('42', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('43', plain, ((v1_funct_1 @ sk_C_2)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.54/0.76          | ((sk_B) = (k1_xboole_0))
% 0.54/0.76          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ sk_B @ X0)
% 0.54/0.76          | ((sk_B) = (k1_xboole_0))
% 0.54/0.76          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.54/0.76             (k2_relat_1 @ sk_C_2)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['37', '44'])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.54/0.76          | (r1_tarski @ sk_B @ X0)
% 0.54/0.76          | ((sk_B) = (k1_xboole_0))
% 0.54/0.76          | (r1_tarski @ sk_B @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['34', '45'])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((sk_B) = (k1_xboole_0))
% 0.54/0.76          | (r1_tarski @ sk_B @ X0)
% 0.54/0.76          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['46'])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (![X1 : $i, X3 : $i]:
% 0.54/0.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.54/0.76        | ((sk_B) = (k1_xboole_0))
% 0.54/0.76        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['49'])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X6 : $i, X8 : $i]:
% 0.54/0.76         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0))
% 0.54/0.76        | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.54/0.76        | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.76  thf('53', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.54/0.76      inference('demod', [status(thm)], ['16', '19'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      ((((sk_B) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 0.54/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.54/0.76  thf('55', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['25', '28'])).
% 0.54/0.76  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.76      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.54/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.76  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('58', plain, ($false),
% 0.54/0.76      inference('demod', [status(thm)], ['31', '56', '57'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
