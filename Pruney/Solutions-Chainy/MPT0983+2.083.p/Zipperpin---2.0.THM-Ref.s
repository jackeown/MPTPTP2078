%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DqlrEvVyUH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:14 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 356 expanded)
%              Number of leaves         :   42 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          : 1185 (6739 expanded)
%              Number of equality atoms :   44 (  98 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('18',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','18'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('20',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('27',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('28',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_relat_1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','37','38','39','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != X25 )
      | ( v2_funct_2 @ X26 @ X25 )
      | ~ ( v5_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v5_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
      | ( v2_funct_2 @ X26 @ ( k2_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','37','38','39','40'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['44','47','48','51'])).

thf('53',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('54',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['22','56'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X34: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('76',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('78',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40 ) )
      | ( v2_funct_1 @ X44 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('90',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('91',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('94',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','92','94','95'])).

thf('97',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['58','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['57','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DqlrEvVyUH
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:43:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.34/3.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.34/3.57  % Solved by: fo/fo7.sh
% 3.34/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.34/3.57  % done 3368 iterations in 3.121s
% 3.34/3.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.34/3.57  % SZS output start Refutation
% 3.34/3.57  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.34/3.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.34/3.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.34/3.57  thf(sk_C_type, type, sk_C: $i).
% 3.34/3.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.34/3.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.34/3.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.34/3.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.34/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.34/3.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.34/3.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.34/3.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.34/3.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.34/3.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.34/3.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.34/3.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.34/3.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.34/3.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.34/3.57  thf(sk_D_type, type, sk_D: $i).
% 3.34/3.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.34/3.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.34/3.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.34/3.57  thf(sk_B_type, type, sk_B: $i > $i).
% 3.34/3.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.34/3.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.34/3.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.34/3.57  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.57  thf(t8_boole, axiom,
% 3.34/3.57    (![A:$i,B:$i]:
% 3.34/3.57     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.34/3.57  thf('1', plain,
% 3.34/3.57      (![X3 : $i, X4 : $i]:
% 3.34/3.57         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t8_boole])).
% 3.34/3.57  thf('2', plain,
% 3.34/3.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.57      inference('sup-', [status(thm)], ['0', '1'])).
% 3.34/3.57  thf(d1_xboole_0, axiom,
% 3.34/3.57    (![A:$i]:
% 3.34/3.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.34/3.57  thf('3', plain,
% 3.34/3.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.57  thf(t113_zfmisc_1, axiom,
% 3.34/3.57    (![A:$i,B:$i]:
% 3.34/3.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.34/3.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.34/3.57  thf('4', plain,
% 3.34/3.57      (![X6 : $i, X7 : $i]:
% 3.34/3.57         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.34/3.57  thf('5', plain,
% 3.34/3.57      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.34/3.57      inference('simplify', [status(thm)], ['4'])).
% 3.34/3.57  thf(dt_k6_partfun1, axiom,
% 3.34/3.57    (![A:$i]:
% 3.34/3.57     ( ( m1_subset_1 @
% 3.34/3.57         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.34/3.57       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.34/3.57  thf('6', plain,
% 3.34/3.57      (![X34 : $i]:
% 3.34/3.57         (m1_subset_1 @ (k6_partfun1 @ X34) @ 
% 3.34/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.34/3.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.34/3.57  thf(redefinition_k6_partfun1, axiom,
% 3.34/3.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.34/3.57  thf('7', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('8', plain,
% 3.34/3.57      (![X34 : $i]:
% 3.34/3.57         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 3.34/3.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.34/3.57      inference('demod', [status(thm)], ['6', '7'])).
% 3.34/3.57  thf('9', plain,
% 3.34/3.57      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.34/3.57      inference('sup+', [status(thm)], ['5', '8'])).
% 3.34/3.57  thf(t5_subset, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.34/3.57          ( v1_xboole_0 @ C ) ) ))).
% 3.34/3.57  thf('10', plain,
% 3.34/3.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.34/3.57         (~ (r2_hidden @ X8 @ X9)
% 3.34/3.57          | ~ (v1_xboole_0 @ X10)
% 3.34/3.57          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.34/3.57      inference('cnf', [status(esa)], [t5_subset])).
% 3.34/3.57  thf('11', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.34/3.57          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['9', '10'])).
% 3.34/3.57  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.57  thf('13', plain,
% 3.34/3.57      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.34/3.57      inference('demod', [status(thm)], ['11', '12'])).
% 3.34/3.57  thf('14', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.34/3.57      inference('sup-', [status(thm)], ['3', '13'])).
% 3.34/3.57  thf('15', plain,
% 3.34/3.57      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.57      inference('sup-', [status(thm)], ['0', '1'])).
% 3.34/3.57  thf('16', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 3.34/3.57      inference('sup-', [status(thm)], ['14', '15'])).
% 3.34/3.57  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.34/3.57  thf('17', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 3.34/3.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.34/3.57  thf('18', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.34/3.57      inference('sup+', [status(thm)], ['16', '17'])).
% 3.34/3.57  thf('19', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.34/3.57      inference('sup+', [status(thm)], ['2', '18'])).
% 3.34/3.57  thf(t29_funct_2, conjecture,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ![D:$i]:
% 3.34/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57           ( ( r2_relset_1 @
% 3.34/3.57               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.57               ( k6_partfun1 @ A ) ) =>
% 3.34/3.57             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.34/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.34/3.57    (~( ![A:$i,B:$i,C:$i]:
% 3.34/3.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57          ( ![D:$i]:
% 3.34/3.57            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57              ( ( r2_relset_1 @
% 3.34/3.57                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.34/3.57                  ( k6_partfun1 @ A ) ) =>
% 3.34/3.57                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.34/3.57    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.34/3.57  thf('20', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('21', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.57      inference('split', [status(esa)], ['20'])).
% 3.34/3.57  thf('22', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.57      inference('sup-', [status(thm)], ['19', '21'])).
% 3.34/3.57  thf('23', plain,
% 3.34/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.57        (k6_partfun1 @ sk_A))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('24', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('25', plain,
% 3.34/3.57      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.57        (k6_relat_1 @ sk_A))),
% 3.34/3.57      inference('demod', [status(thm)], ['23', '24'])).
% 3.34/3.57  thf('26', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(t24_funct_2, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.34/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.57       ( ![D:$i]:
% 3.34/3.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.34/3.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.34/3.57           ( ( r2_relset_1 @
% 3.34/3.57               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.34/3.57               ( k6_partfun1 @ B ) ) =>
% 3.34/3.57             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.34/3.57  thf('27', plain,
% 3.34/3.57      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X36)
% 3.34/3.57          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 3.34/3.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.34/3.57          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 3.34/3.57               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 3.34/3.57               (k6_partfun1 @ X37))
% 3.34/3.57          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 3.34/3.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 3.34/3.57          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 3.34/3.57          | ~ (v1_funct_1 @ X39))),
% 3.34/3.57      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.34/3.57  thf('28', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.34/3.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.34/3.57  thf('29', plain,
% 3.34/3.57      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X36)
% 3.34/3.57          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 3.34/3.57          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.34/3.57          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 3.34/3.57               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 3.34/3.57               (k6_relat_1 @ X37))
% 3.34/3.57          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 3.34/3.57          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 3.34/3.57          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 3.34/3.57          | ~ (v1_funct_1 @ X39))),
% 3.34/3.57      inference('demod', [status(thm)], ['27', '28'])).
% 3.34/3.57  thf('30', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.34/3.57          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.34/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.34/3.57               (k6_relat_1 @ sk_A))
% 3.34/3.57          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.34/3.57          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.57      inference('sup-', [status(thm)], ['26', '29'])).
% 3.34/3.57  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf('33', plain,
% 3.34/3.57      (![X0 : $i]:
% 3.34/3.57         (~ (v1_funct_1 @ X0)
% 3.34/3.57          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.34/3.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.34/3.57          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.34/3.57          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.57               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.34/3.57               (k6_relat_1 @ sk_A)))),
% 3.34/3.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 3.34/3.57  thf('34', plain,
% 3.34/3.57      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.34/3.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.34/3.57        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.57        | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.57      inference('sup-', [status(thm)], ['25', '33'])).
% 3.34/3.57  thf('35', plain,
% 3.34/3.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.57  thf(redefinition_k2_relset_1, axiom,
% 3.34/3.57    (![A:$i,B:$i,C:$i]:
% 3.34/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.34/3.58  thf('36', plain,
% 3.34/3.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.34/3.58         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 3.34/3.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.34/3.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.34/3.58  thf('37', plain,
% 3.34/3.58      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.34/3.58      inference('sup-', [status(thm)], ['35', '36'])).
% 3.34/3.58  thf('38', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('41', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.58      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 3.34/3.58  thf(d3_funct_2, axiom,
% 3.34/3.58    (![A:$i,B:$i]:
% 3.34/3.58     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.34/3.58       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.34/3.58  thf('42', plain,
% 3.34/3.58      (![X25 : $i, X26 : $i]:
% 3.34/3.58         (((k2_relat_1 @ X26) != (X25))
% 3.34/3.58          | (v2_funct_2 @ X26 @ X25)
% 3.34/3.58          | ~ (v5_relat_1 @ X26 @ X25)
% 3.34/3.58          | ~ (v1_relat_1 @ X26))),
% 3.34/3.58      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.34/3.58  thf('43', plain,
% 3.34/3.58      (![X26 : $i]:
% 3.34/3.58         (~ (v1_relat_1 @ X26)
% 3.34/3.58          | ~ (v5_relat_1 @ X26 @ (k2_relat_1 @ X26))
% 3.34/3.58          | (v2_funct_2 @ X26 @ (k2_relat_1 @ X26)))),
% 3.34/3.58      inference('simplify', [status(thm)], ['42'])).
% 3.34/3.58  thf('44', plain,
% 3.34/3.58      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.34/3.58        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.34/3.58        | ~ (v1_relat_1 @ sk_D))),
% 3.34/3.58      inference('sup-', [status(thm)], ['41', '43'])).
% 3.34/3.58  thf('45', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf(cc2_relset_1, axiom,
% 3.34/3.58    (![A:$i,B:$i,C:$i]:
% 3.34/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.34/3.58  thf('46', plain,
% 3.34/3.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.34/3.58         ((v5_relat_1 @ X15 @ X17)
% 3.34/3.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.34/3.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.34/3.58  thf('47', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.34/3.58      inference('sup-', [status(thm)], ['45', '46'])).
% 3.34/3.58  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.34/3.58      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 3.34/3.58  thf('49', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf(cc1_relset_1, axiom,
% 3.34/3.58    (![A:$i,B:$i,C:$i]:
% 3.34/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.34/3.58       ( v1_relat_1 @ C ) ))).
% 3.34/3.58  thf('50', plain,
% 3.34/3.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.34/3.58         ((v1_relat_1 @ X12)
% 3.34/3.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 3.34/3.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.34/3.58  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 3.34/3.58      inference('sup-', [status(thm)], ['49', '50'])).
% 3.34/3.58  thf('52', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.34/3.58      inference('demod', [status(thm)], ['44', '47', '48', '51'])).
% 3.34/3.58  thf('53', plain,
% 3.34/3.58      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.34/3.58      inference('split', [status(esa)], ['20'])).
% 3.34/3.58  thf('54', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.58      inference('sup-', [status(thm)], ['52', '53'])).
% 3.34/3.58  thf('55', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.34/3.58      inference('split', [status(esa)], ['20'])).
% 3.34/3.58  thf('56', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.34/3.58      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 3.34/3.58  thf('57', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.34/3.58      inference('simpl_trail', [status(thm)], ['22', '56'])).
% 3.34/3.58  thf('58', plain,
% 3.34/3.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.34/3.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.34/3.58  thf('59', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('60', plain,
% 3.34/3.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.34/3.58         (~ (r2_hidden @ X8 @ X9)
% 3.34/3.58          | ~ (v1_xboole_0 @ X10)
% 3.34/3.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.34/3.58      inference('cnf', [status(esa)], [t5_subset])).
% 3.34/3.58  thf('61', plain,
% 3.34/3.58      (![X0 : $i]:
% 3.34/3.58         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.34/3.58          | ~ (r2_hidden @ X0 @ sk_C))),
% 3.34/3.58      inference('sup-', [status(thm)], ['59', '60'])).
% 3.34/3.58  thf('62', plain,
% 3.34/3.58      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.58        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.58        (k6_relat_1 @ sk_A))),
% 3.34/3.58      inference('demod', [status(thm)], ['23', '24'])).
% 3.34/3.58  thf('63', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('64', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf(dt_k1_partfun1, axiom,
% 3.34/3.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.34/3.58     ( ( ( v1_funct_1 @ E ) & 
% 3.34/3.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.58         ( v1_funct_1 @ F ) & 
% 3.34/3.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.34/3.58       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.34/3.58         ( m1_subset_1 @
% 3.34/3.58           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.34/3.58           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.34/3.58  thf('65', plain,
% 3.34/3.58      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.34/3.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.34/3.58          | ~ (v1_funct_1 @ X27)
% 3.34/3.58          | ~ (v1_funct_1 @ X30)
% 3.34/3.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 3.34/3.58          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 3.34/3.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 3.34/3.58      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.34/3.58  thf('66', plain,
% 3.34/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.34/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.34/3.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.34/3.58          | ~ (v1_funct_1 @ X1)
% 3.34/3.58          | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.58      inference('sup-', [status(thm)], ['64', '65'])).
% 3.34/3.58  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('68', plain,
% 3.34/3.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.34/3.58         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.34/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.34/3.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.34/3.58          | ~ (v1_funct_1 @ X1))),
% 3.34/3.58      inference('demod', [status(thm)], ['66', '67'])).
% 3.34/3.58  thf('69', plain,
% 3.34/3.58      ((~ (v1_funct_1 @ sk_D)
% 3.34/3.58        | (m1_subset_1 @ 
% 3.34/3.58           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.34/3.58      inference('sup-', [status(thm)], ['63', '68'])).
% 3.34/3.58  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('71', plain,
% 3.34/3.58      ((m1_subset_1 @ 
% 3.34/3.58        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.34/3.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.34/3.58      inference('demod', [status(thm)], ['69', '70'])).
% 3.34/3.58  thf(redefinition_r2_relset_1, axiom,
% 3.34/3.58    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.58     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.34/3.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.58       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.34/3.58  thf('72', plain,
% 3.34/3.58      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 3.34/3.58         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.34/3.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 3.34/3.58          | ((X21) = (X24))
% 3.34/3.58          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 3.34/3.58      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.34/3.58  thf('73', plain,
% 3.34/3.58      (![X0 : $i]:
% 3.34/3.58         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.34/3.58             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 3.34/3.58          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 3.34/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.34/3.58      inference('sup-', [status(thm)], ['71', '72'])).
% 3.34/3.58  thf('74', plain,
% 3.34/3.58      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.34/3.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.34/3.58        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.34/3.58            = (k6_relat_1 @ sk_A)))),
% 3.34/3.58      inference('sup-', [status(thm)], ['62', '73'])).
% 3.34/3.58  thf('75', plain,
% 3.34/3.58      (![X34 : $i]:
% 3.34/3.58         (m1_subset_1 @ (k6_relat_1 @ X34) @ 
% 3.34/3.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))),
% 3.34/3.58      inference('demod', [status(thm)], ['6', '7'])).
% 3.34/3.58  thf('76', plain,
% 3.34/3.58      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.34/3.58         = (k6_relat_1 @ sk_A))),
% 3.34/3.58      inference('demod', [status(thm)], ['74', '75'])).
% 3.34/3.58  thf('77', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf(t26_funct_2, axiom,
% 3.34/3.58    (![A:$i,B:$i,C:$i,D:$i]:
% 3.34/3.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.34/3.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.34/3.58       ( ![E:$i]:
% 3.34/3.58         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.34/3.58             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.34/3.58           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.34/3.58             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.34/3.58               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.34/3.58  thf('78', plain,
% 3.34/3.58      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.34/3.58         (~ (v1_funct_1 @ X40)
% 3.34/3.58          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 3.34/3.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.34/3.58          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 3.34/3.58          | (v2_funct_1 @ X44)
% 3.34/3.58          | ((X42) = (k1_xboole_0))
% 3.34/3.58          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 3.34/3.58          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 3.34/3.58          | ~ (v1_funct_1 @ X44))),
% 3.34/3.58      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.34/3.58  thf('79', plain,
% 3.34/3.58      (![X0 : $i, X1 : $i]:
% 3.34/3.58         (~ (v1_funct_1 @ X0)
% 3.34/3.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.34/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.34/3.58          | ((sk_A) = (k1_xboole_0))
% 3.34/3.58          | (v2_funct_1 @ X0)
% 3.34/3.58          | ~ (v2_funct_1 @ 
% 3.34/3.58               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.34/3.58          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.34/3.58          | ~ (v1_funct_1 @ sk_D))),
% 3.34/3.58      inference('sup-', [status(thm)], ['77', '78'])).
% 3.34/3.58  thf('80', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('82', plain,
% 3.34/3.58      (![X0 : $i, X1 : $i]:
% 3.34/3.58         (~ (v1_funct_1 @ X0)
% 3.34/3.58          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.34/3.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.34/3.58          | ((sk_A) = (k1_xboole_0))
% 3.34/3.58          | (v2_funct_1 @ X0)
% 3.34/3.58          | ~ (v2_funct_1 @ 
% 3.34/3.58               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.34/3.58      inference('demod', [status(thm)], ['79', '80', '81'])).
% 3.34/3.58  thf('83', plain,
% 3.34/3.58      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.34/3.58        | (v2_funct_1 @ sk_C)
% 3.34/3.58        | ((sk_A) = (k1_xboole_0))
% 3.34/3.58        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.34/3.58        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.34/3.58        | ~ (v1_funct_1 @ sk_C))),
% 3.34/3.58      inference('sup-', [status(thm)], ['76', '82'])).
% 3.34/3.58  thf('84', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 3.34/3.58      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.34/3.58  thf('85', plain,
% 3.34/3.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('86', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 3.34/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.34/3.58  thf('88', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.34/3.58      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 3.34/3.58  thf('89', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.34/3.58      inference('split', [status(esa)], ['20'])).
% 3.34/3.58  thf('90', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.34/3.58      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 3.34/3.58  thf('91', plain, (~ (v2_funct_1 @ sk_C)),
% 3.34/3.58      inference('simpl_trail', [status(thm)], ['89', '90'])).
% 3.34/3.58  thf('92', plain, (((sk_A) = (k1_xboole_0))),
% 3.34/3.58      inference('clc', [status(thm)], ['88', '91'])).
% 3.34/3.58  thf('93', plain,
% 3.34/3.58      (![X6 : $i, X7 : $i]:
% 3.34/3.58         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.34/3.58      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.34/3.58  thf('94', plain,
% 3.34/3.58      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.34/3.58      inference('simplify', [status(thm)], ['93'])).
% 3.34/3.58  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.34/3.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.34/3.58  thf('96', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 3.34/3.58      inference('demod', [status(thm)], ['61', '92', '94', '95'])).
% 3.34/3.58  thf('97', plain, ((v1_xboole_0 @ sk_C)),
% 3.34/3.58      inference('sup-', [status(thm)], ['58', '96'])).
% 3.34/3.58  thf('98', plain, ($false), inference('demod', [status(thm)], ['57', '97'])).
% 3.34/3.58  
% 3.34/3.58  % SZS output end Refutation
% 3.34/3.58  
% 3.34/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
