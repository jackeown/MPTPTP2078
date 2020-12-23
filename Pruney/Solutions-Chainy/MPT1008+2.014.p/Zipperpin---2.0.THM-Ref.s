%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sZfoAeuOg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 734 expanded)
%              Number of leaves         :   40 ( 236 expanded)
%              Depth                    :   19
%              Number of atoms          :  894 (9125 expanded)
%              Number of equality atoms :   89 ( 650 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X41 @ X38 ) @ ( k2_relset_1 @ X39 @ X40 @ X41 ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X37 @ X35 )
        = ( k2_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20
        = ( k7_relat_1 @ X20 @ X21 ) )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k11_relat_1 @ X18 @ X19 )
        = k1_xboole_0 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t168_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X26 ) )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ ( k1_tarski @ X25 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t168_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) ) )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k11_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ X14 @ ( k1_tarski @ X15 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('31',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k11_relat_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','38','39'])).

thf('41',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['14','44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != ( k1_tarski @ X23 ) )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_tarski @ ( k1_funct_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k9_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('59',plain,(
    ! [X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('63',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('66',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf('68',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('73',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('74',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','75'])).

thf('77',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

thf('80',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('82',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5sZfoAeuOg
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:21:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 134 iterations in 0.080s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X1 : $i, X3 : $i]:
% 0.20/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf(t62_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.53         ( m1_subset_1 @
% 0.20/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.53            ( m1_subset_1 @
% 0.20/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t6_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X38 @ X39)
% 0.20/0.53          | ((X40) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_funct_1 @ X41)
% 0.20/0.53          | ~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.20/0.53          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ X41 @ X38) @ 
% 0.20/0.53             (k2_relset_1 @ X39 @ X40 @ X41)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.20/0.53           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X36 @ X37 @ X35) = (k2_relat_1 @ X35))
% 0.20/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.53         = (k2_relat_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.20/0.53  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.20/0.53             (k2_relat_1 @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.20/0.53          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.20/0.53               (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X32 @ X33)
% 0.20/0.53          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('17', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t209_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (((X20) = (k7_relat_1 @ X20 @ X21))
% 0.20/0.53          | ~ (v4_relat_1 @ X20 @ X21)
% 0.20/0.53          | ~ (v1_relat_1 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( v1_relat_1 @ C ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((v1_relat_1 @ X29)
% 0.20/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.53  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf(t205_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (((k11_relat_1 @ X18 @ X19) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 0.20/0.53          | ~ (v1_relat_1 @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.53  thf(t168_funct_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.53         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.20/0.53           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X25 @ (k1_relat_1 @ X26))
% 0.20/0.53          | ((k2_relat_1 @ (k7_relat_1 @ X26 @ (k1_tarski @ X25)))
% 0.20/0.53              = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.20/0.53          | ~ (v1_funct_1 @ X26)
% 0.20/0.53          | ~ (v1_relat_1 @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t168_funct_1])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.20/0.53              = (k1_tarski @ (k1_funct_1 @ X0 @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_tarski @ X1)))
% 0.20/0.53            = (k1_tarski @ (k1_funct_1 @ X0 @ X1)))
% 0.20/0.53          | ~ (v1_funct_1 @ X0)
% 0.20/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.53        | ((k11_relat_1 @ sk_C_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.53        | ~ (v1_funct_1 @ sk_C_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '27'])).
% 0.20/0.53  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(d16_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (((k11_relat_1 @ X14 @ X15) = (k9_relat_1 @ X14 @ (k1_tarski @ X15)))
% 0.20/0.53          | ~ (v1_relat_1 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.53  thf('31', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.53  thf(t148_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.20/0.53          | ~ (v1_relat_1 @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['30', '35'])).
% 0.20/0.54  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('38', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.20/0.54        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29', '38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.54         = (k2_relat_1 @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('46', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '44', '45'])).
% 0.20/0.54  thf('47', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X4 : $i, X6 : $i]:
% 0.20/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.54  thf(t60_relat_1, axiom,
% 0.20/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf(t14_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i]:
% 0.20/0.54         (((k1_relat_1 @ X24) != (k1_tarski @ X23))
% 0.20/0.54          | ((k2_relat_1 @ X24) = (k1_tarski @ (k1_funct_1 @ X24 @ X23)))
% 0.20/0.54          | ~ (v1_funct_1 @ X24)
% 0.20/0.54          | ~ (v1_relat_1 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.54          | ((k2_relat_1 @ k1_xboole_0)
% 0.20/0.54              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X16 @ X17)) = (k9_relat_1 @ X16 @ X17))
% 0.20/0.54          | ~ (v1_relat_1 @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf(t64_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X22 : $i]:
% 0.20/0.54         (((k2_relat_1 @ X22) != (k1_xboole_0))
% 0.20/0.54          | ((X22) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.54          | ~ (v1_relat_1 @ X1)
% 0.20/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54        | ((k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.54        | ((k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '60'])).
% 0.20/0.54  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('63', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.54  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      ((((sk_C_1) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C_1) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.20/0.54  thf('67', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      ((((sk_C_1) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.54      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.54  thf('70', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['56', '69'])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '70'])).
% 0.20/0.54  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.54  thf('73', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.54  thf('74', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.54          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.54      inference('demod', [status(thm)], ['71', '74'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['76'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('79', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('81', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
