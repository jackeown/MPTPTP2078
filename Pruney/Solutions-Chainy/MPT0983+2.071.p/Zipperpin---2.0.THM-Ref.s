%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D17F3163jT

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:12 EST 2020

% Result     : Theorem 4.53s
% Output     : Refutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 302 expanded)
%              Number of leaves         :   48 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          : 1199 (4654 expanded)
%              Number of equality atoms :   41 (  74 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l222_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[l222_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('10',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['5','12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('20',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

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

thf('24',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49 ) @ ( k6_partfun1 @ X47 ) )
      | ( ( k2_relset_1 @ X48 @ X47 @ X49 )
        = X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X47 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('46',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ X38 )
       != X37 )
      | ( v2_funct_2 @ X38 @ X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('47',plain,(
    ! [X38: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v5_relat_1 @ X38 @ ( k2_relat_1 @ X38 ) )
      | ( v2_funct_2 @ X38 @ ( k2_relat_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['41','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('56',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('58',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['26','58'])).

thf('60',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('69',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('76',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('79',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('80',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50 ) )
      | ( v2_funct_1 @ X54 )
      | ( X52 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X53 @ X51 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('91',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['24'])).

thf('96',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('97',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['5','12','13'])).

thf('100',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('101',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','98','103'])).

thf('105',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['60','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['59','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D17F3163jT
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:29:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.53/4.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.53/4.71  % Solved by: fo/fo7.sh
% 4.53/4.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.53/4.71  % done 3458 iterations in 4.253s
% 4.53/4.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.53/4.71  % SZS output start Refutation
% 4.53/4.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.53/4.71  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.53/4.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.53/4.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.53/4.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.53/4.71  thf(sk_D_type, type, sk_D: $i).
% 4.53/4.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.53/4.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.53/4.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.53/4.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.53/4.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.53/4.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.53/4.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.53/4.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.53/4.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.53/4.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.53/4.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.53/4.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.53/4.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.53/4.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.53/4.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.53/4.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.53/4.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.53/4.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.53/4.71  thf(sk_B_type, type, sk_B: $i > $i).
% 4.53/4.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.53/4.71  thf(sk_A_type, type, sk_A: $i).
% 4.53/4.71  thf(d3_tarski, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( r1_tarski @ A @ B ) <=>
% 4.53/4.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.53/4.71  thf('0', plain,
% 4.53/4.71      (![X4 : $i, X6 : $i]:
% 4.53/4.71         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 4.53/4.71      inference('cnf', [status(esa)], [d3_tarski])).
% 4.53/4.71  thf(d1_xboole_0, axiom,
% 4.53/4.71    (![A:$i]:
% 4.53/4.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.53/4.71  thf('1', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.53/4.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.53/4.71  thf('2', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.53/4.71      inference('sup-', [status(thm)], ['0', '1'])).
% 4.53/4.71  thf(l222_relat_1, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 4.53/4.71  thf('3', plain, (![X17 : $i]: (v5_relat_1 @ k1_xboole_0 @ X17)),
% 4.53/4.71      inference('cnf', [status(esa)], [l222_relat_1])).
% 4.53/4.71  thf(d19_relat_1, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( v1_relat_1 @ B ) =>
% 4.53/4.71       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.53/4.71  thf('4', plain,
% 4.53/4.71      (![X15 : $i, X16 : $i]:
% 4.53/4.71         (~ (v5_relat_1 @ X15 @ X16)
% 4.53/4.71          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.53/4.71          | ~ (v1_relat_1 @ X15))),
% 4.53/4.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.53/4.71  thf('5', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_relat_1 @ k1_xboole_0)
% 4.53/4.71          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 4.53/4.71      inference('sup-', [status(thm)], ['3', '4'])).
% 4.53/4.71  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 4.53/4.71  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.53/4.71      inference('cnf', [status(esa)], [t81_relat_1])).
% 4.53/4.71  thf(redefinition_k6_partfun1, axiom,
% 4.53/4.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.53/4.71  thf('7', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.53/4.71  thf('8', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.53/4.71      inference('demod', [status(thm)], ['6', '7'])).
% 4.53/4.71  thf(fc4_funct_1, axiom,
% 4.53/4.71    (![A:$i]:
% 4.53/4.71     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.53/4.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.53/4.71  thf('9', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 4.53/4.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.53/4.71  thf('10', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.53/4.71  thf('11', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 4.53/4.71      inference('demod', [status(thm)], ['9', '10'])).
% 4.53/4.71  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.53/4.71      inference('sup+', [status(thm)], ['8', '11'])).
% 4.53/4.71  thf(t60_relat_1, axiom,
% 4.53/4.71    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 4.53/4.71     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.53/4.71  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.53/4.71      inference('cnf', [status(esa)], [t60_relat_1])).
% 4.53/4.71  thf('14', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.53/4.71      inference('demod', [status(thm)], ['5', '12', '13'])).
% 4.53/4.71  thf(d10_xboole_0, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.53/4.71  thf('15', plain,
% 4.53/4.71      (![X7 : $i, X9 : $i]:
% 4.53/4.71         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.53/4.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.53/4.71  thf('16', plain,
% 4.53/4.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['14', '15'])).
% 4.53/4.71  thf('17', plain,
% 4.53/4.71      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['2', '16'])).
% 4.53/4.71  thf('18', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.53/4.71      inference('demod', [status(thm)], ['6', '7'])).
% 4.53/4.71  thf('19', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 4.53/4.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.53/4.71  thf('20', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.53/4.71  thf('21', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 4.53/4.71      inference('demod', [status(thm)], ['19', '20'])).
% 4.53/4.71  thf('22', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.53/4.71      inference('sup+', [status(thm)], ['18', '21'])).
% 4.53/4.71  thf('23', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.53/4.71      inference('sup+', [status(thm)], ['17', '22'])).
% 4.53/4.71  thf(t29_funct_2, conjecture,
% 4.53/4.71    (![A:$i,B:$i,C:$i]:
% 4.53/4.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.53/4.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.53/4.71       ( ![D:$i]:
% 4.53/4.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.53/4.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.53/4.71           ( ( r2_relset_1 @
% 4.53/4.71               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.53/4.71               ( k6_partfun1 @ A ) ) =>
% 4.53/4.71             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.53/4.71  thf(zf_stmt_0, negated_conjecture,
% 4.53/4.71    (~( ![A:$i,B:$i,C:$i]:
% 4.53/4.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.53/4.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.53/4.71          ( ![D:$i]:
% 4.53/4.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.53/4.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.53/4.71              ( ( r2_relset_1 @
% 4.53/4.71                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.53/4.71                  ( k6_partfun1 @ A ) ) =>
% 4.53/4.71                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.53/4.71    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.53/4.71  thf('24', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('25', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.53/4.71      inference('split', [status(esa)], ['24'])).
% 4.53/4.71  thf('26', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['23', '25'])).
% 4.53/4.71  thf('27', plain,
% 4.53/4.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.53/4.71        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.53/4.71        (k6_partfun1 @ sk_A))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('28', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(t24_funct_2, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i]:
% 4.53/4.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.53/4.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.53/4.71       ( ![D:$i]:
% 4.53/4.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.53/4.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.53/4.71           ( ( r2_relset_1 @
% 4.53/4.71               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.53/4.71               ( k6_partfun1 @ B ) ) =>
% 4.53/4.71             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.53/4.71  thf('29', plain,
% 4.53/4.71      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X46)
% 4.53/4.71          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 4.53/4.71          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 4.53/4.71          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 4.53/4.71               (k1_partfun1 @ X47 @ X48 @ X48 @ X47 @ X46 @ X49) @ 
% 4.53/4.71               (k6_partfun1 @ X47))
% 4.53/4.71          | ((k2_relset_1 @ X48 @ X47 @ X49) = (X47))
% 4.53/4.71          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 4.53/4.71          | ~ (v1_funct_2 @ X49 @ X48 @ X47)
% 4.53/4.71          | ~ (v1_funct_1 @ X49))),
% 4.53/4.71      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.53/4.71  thf('30', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X0)
% 4.53/4.71          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 4.53/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.53/4.71          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 4.53/4.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.53/4.71               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 4.53/4.71               (k6_partfun1 @ sk_A))
% 4.53/4.71          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 4.53/4.71          | ~ (v1_funct_1 @ sk_C_1))),
% 4.53/4.71      inference('sup-', [status(thm)], ['28', '29'])).
% 4.53/4.71  thf('31', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('33', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X0)
% 4.53/4.71          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 4.53/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.53/4.71          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 4.53/4.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.53/4.71               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ X0) @ 
% 4.53/4.71               (k6_partfun1 @ sk_A)))),
% 4.53/4.71      inference('demod', [status(thm)], ['30', '31', '32'])).
% 4.53/4.71  thf('34', plain,
% 4.53/4.71      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 4.53/4.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 4.53/4.71        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 4.53/4.71        | ~ (v1_funct_1 @ sk_D))),
% 4.53/4.71      inference('sup-', [status(thm)], ['27', '33'])).
% 4.53/4.71  thf('35', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(redefinition_k2_relset_1, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i]:
% 4.53/4.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.53/4.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.53/4.71  thf('36', plain,
% 4.53/4.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.53/4.71         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 4.53/4.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.53/4.71  thf('37', plain,
% 4.53/4.71      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.53/4.71      inference('sup-', [status(thm)], ['35', '36'])).
% 4.53/4.71  thf('38', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('41', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.53/4.71      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 4.53/4.71  thf('42', plain,
% 4.53/4.71      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 4.53/4.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.53/4.71  thf('43', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.53/4.71      inference('simplify', [status(thm)], ['42'])).
% 4.53/4.71  thf('44', plain,
% 4.53/4.71      (![X15 : $i, X16 : $i]:
% 4.53/4.71         (~ (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 4.53/4.71          | (v5_relat_1 @ X15 @ X16)
% 4.53/4.71          | ~ (v1_relat_1 @ X15))),
% 4.53/4.71      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.53/4.71  thf('45', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['43', '44'])).
% 4.53/4.71  thf(d3_funct_2, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.53/4.71       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.53/4.71  thf('46', plain,
% 4.53/4.71      (![X37 : $i, X38 : $i]:
% 4.53/4.71         (((k2_relat_1 @ X38) != (X37))
% 4.53/4.71          | (v2_funct_2 @ X38 @ X37)
% 4.53/4.71          | ~ (v5_relat_1 @ X38 @ X37)
% 4.53/4.71          | ~ (v1_relat_1 @ X38))),
% 4.53/4.71      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.53/4.71  thf('47', plain,
% 4.53/4.71      (![X38 : $i]:
% 4.53/4.71         (~ (v1_relat_1 @ X38)
% 4.53/4.71          | ~ (v5_relat_1 @ X38 @ (k2_relat_1 @ X38))
% 4.53/4.71          | (v2_funct_2 @ X38 @ (k2_relat_1 @ X38)))),
% 4.53/4.71      inference('simplify', [status(thm)], ['46'])).
% 4.53/4.71  thf('48', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_relat_1 @ X0)
% 4.53/4.71          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 4.53/4.71          | ~ (v1_relat_1 @ X0))),
% 4.53/4.71      inference('sup-', [status(thm)], ['45', '47'])).
% 4.53/4.71  thf('49', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 4.53/4.71      inference('simplify', [status(thm)], ['48'])).
% 4.53/4.71  thf('50', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 4.53/4.71      inference('sup+', [status(thm)], ['41', '49'])).
% 4.53/4.71  thf('51', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(cc1_relset_1, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i]:
% 4.53/4.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.53/4.71       ( v1_relat_1 @ C ) ))).
% 4.53/4.71  thf('52', plain,
% 4.53/4.71      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.53/4.71         ((v1_relat_1 @ X23)
% 4.53/4.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.53/4.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.53/4.71  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 4.53/4.71      inference('sup-', [status(thm)], ['51', '52'])).
% 4.53/4.71  thf('54', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.53/4.71      inference('demod', [status(thm)], ['50', '53'])).
% 4.53/4.71  thf('55', plain,
% 4.53/4.71      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.53/4.71      inference('split', [status(esa)], ['24'])).
% 4.53/4.71  thf('56', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.53/4.71      inference('sup-', [status(thm)], ['54', '55'])).
% 4.53/4.71  thf('57', plain,
% 4.53/4.71      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.53/4.71      inference('split', [status(esa)], ['24'])).
% 4.53/4.71  thf('58', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.53/4.71      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 4.53/4.71  thf('59', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 4.53/4.71      inference('simpl_trail', [status(thm)], ['26', '58'])).
% 4.53/4.71  thf('60', plain,
% 4.53/4.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.53/4.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.53/4.71  thf(fc4_zfmisc_1, axiom,
% 4.53/4.71    (![A:$i,B:$i]:
% 4.53/4.71     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.53/4.71  thf('61', plain,
% 4.53/4.71      (![X10 : $i, X11 : $i]:
% 4.53/4.71         (~ (v1_xboole_0 @ X10) | (v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 4.53/4.71      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.53/4.71  thf('62', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(t5_subset, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i]:
% 4.53/4.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.53/4.71          ( v1_xboole_0 @ C ) ) ))).
% 4.53/4.71  thf('63', plain,
% 4.53/4.71      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.53/4.71         (~ (r2_hidden @ X12 @ X13)
% 4.53/4.71          | ~ (v1_xboole_0 @ X14)
% 4.53/4.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 4.53/4.71      inference('cnf', [status(esa)], [t5_subset])).
% 4.53/4.71  thf('64', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 4.53/4.71          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.53/4.71      inference('sup-', [status(thm)], ['62', '63'])).
% 4.53/4.71  thf('65', plain,
% 4.53/4.71      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.53/4.71      inference('sup-', [status(thm)], ['61', '64'])).
% 4.53/4.71  thf('66', plain,
% 4.53/4.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.53/4.71        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.53/4.71        (k6_partfun1 @ sk_A))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('67', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('68', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(dt_k1_partfun1, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.53/4.71     ( ( ( v1_funct_1 @ E ) & 
% 4.53/4.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.53/4.71         ( v1_funct_1 @ F ) & 
% 4.53/4.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.53/4.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.53/4.71         ( m1_subset_1 @
% 4.53/4.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.53/4.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.53/4.71  thf('69', plain,
% 4.53/4.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.53/4.71         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 4.53/4.71          | ~ (v1_funct_1 @ X39)
% 4.53/4.71          | ~ (v1_funct_1 @ X42)
% 4.53/4.71          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 4.53/4.71          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 4.53/4.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 4.53/4.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.53/4.71  thf('70', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.53/4.71         ((m1_subset_1 @ 
% 4.53/4.71           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.53/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.53/4.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.53/4.71          | ~ (v1_funct_1 @ X1)
% 4.53/4.71          | ~ (v1_funct_1 @ sk_C_1))),
% 4.53/4.71      inference('sup-', [status(thm)], ['68', '69'])).
% 4.53/4.71  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('72', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.53/4.71         ((m1_subset_1 @ 
% 4.53/4.71           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.53/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.53/4.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.53/4.71          | ~ (v1_funct_1 @ X1))),
% 4.53/4.71      inference('demod', [status(thm)], ['70', '71'])).
% 4.53/4.71  thf('73', plain,
% 4.53/4.71      ((~ (v1_funct_1 @ sk_D)
% 4.53/4.71        | (m1_subset_1 @ 
% 4.53/4.71           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.53/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.53/4.71      inference('sup-', [status(thm)], ['67', '72'])).
% 4.53/4.71  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('75', plain,
% 4.53/4.71      ((m1_subset_1 @ 
% 4.53/4.71        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.53/4.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.53/4.71      inference('demod', [status(thm)], ['73', '74'])).
% 4.53/4.71  thf(redefinition_r2_relset_1, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i,D:$i]:
% 4.53/4.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.53/4.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.53/4.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.53/4.71  thf('76', plain,
% 4.53/4.71      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 4.53/4.71         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.53/4.71          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.53/4.71          | ((X32) = (X35))
% 4.53/4.71          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.53/4.71  thf('77', plain,
% 4.53/4.71      (![X0 : $i]:
% 4.53/4.71         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.53/4.71             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 4.53/4.71          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.53/4.71              = (X0))
% 4.53/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.53/4.71      inference('sup-', [status(thm)], ['75', '76'])).
% 4.53/4.71  thf('78', plain,
% 4.53/4.71      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.53/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.53/4.71        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.53/4.71            = (k6_partfun1 @ sk_A)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['66', '77'])).
% 4.53/4.71  thf(t29_relset_1, axiom,
% 4.53/4.71    (![A:$i]:
% 4.53/4.71     ( m1_subset_1 @
% 4.53/4.71       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.53/4.71  thf('79', plain,
% 4.53/4.71      (![X36 : $i]:
% 4.53/4.71         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 4.53/4.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 4.53/4.71      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.53/4.71  thf('80', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 4.53/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.53/4.71  thf('81', plain,
% 4.53/4.71      (![X36 : $i]:
% 4.53/4.71         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 4.53/4.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 4.53/4.71      inference('demod', [status(thm)], ['79', '80'])).
% 4.53/4.71  thf('82', plain,
% 4.53/4.71      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 4.53/4.71         = (k6_partfun1 @ sk_A))),
% 4.53/4.71      inference('demod', [status(thm)], ['78', '81'])).
% 4.53/4.71  thf('83', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf(t26_funct_2, axiom,
% 4.53/4.71    (![A:$i,B:$i,C:$i,D:$i]:
% 4.53/4.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.53/4.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.53/4.71       ( ![E:$i]:
% 4.53/4.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.53/4.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.53/4.71           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.53/4.71             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.53/4.71               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.53/4.71  thf('84', plain,
% 4.53/4.71      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X50)
% 4.53/4.71          | ~ (v1_funct_2 @ X50 @ X51 @ X52)
% 4.53/4.71          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 4.53/4.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X51 @ X51 @ X52 @ X54 @ X50))
% 4.53/4.71          | (v2_funct_1 @ X54)
% 4.53/4.71          | ((X52) = (k1_xboole_0))
% 4.53/4.71          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 4.53/4.71          | ~ (v1_funct_2 @ X54 @ X53 @ X51)
% 4.53/4.71          | ~ (v1_funct_1 @ X54))),
% 4.53/4.71      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.53/4.71  thf('85', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X0)
% 4.53/4.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.53/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.53/4.71          | ((sk_A) = (k1_xboole_0))
% 4.53/4.71          | (v2_funct_1 @ X0)
% 4.53/4.71          | ~ (v2_funct_1 @ 
% 4.53/4.71               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 4.53/4.71          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 4.53/4.71          | ~ (v1_funct_1 @ sk_D))),
% 4.53/4.71      inference('sup-', [status(thm)], ['83', '84'])).
% 4.53/4.71  thf('86', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('88', plain,
% 4.53/4.71      (![X0 : $i, X1 : $i]:
% 4.53/4.71         (~ (v1_funct_1 @ X0)
% 4.53/4.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 4.53/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 4.53/4.71          | ((sk_A) = (k1_xboole_0))
% 4.53/4.71          | (v2_funct_1 @ X0)
% 4.53/4.71          | ~ (v2_funct_1 @ 
% 4.53/4.71               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 4.53/4.71      inference('demod', [status(thm)], ['85', '86', '87'])).
% 4.53/4.71  thf('89', plain,
% 4.53/4.71      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.53/4.71        | (v2_funct_1 @ sk_C_1)
% 4.53/4.71        | ((sk_A) = (k1_xboole_0))
% 4.53/4.71        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.53/4.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 4.53/4.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 4.53/4.71        | ~ (v1_funct_1 @ sk_C_1))),
% 4.53/4.71      inference('sup-', [status(thm)], ['82', '88'])).
% 4.53/4.71  thf('90', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 4.53/4.71      inference('demod', [status(thm)], ['19', '20'])).
% 4.53/4.71  thf('91', plain,
% 4.53/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('92', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('93', plain, ((v1_funct_1 @ sk_C_1)),
% 4.53/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.53/4.71  thf('94', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 4.53/4.71      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 4.53/4.71  thf('95', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.53/4.71      inference('split', [status(esa)], ['24'])).
% 4.53/4.71  thf('96', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.53/4.71      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 4.53/4.71  thf('97', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.53/4.71      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 4.53/4.71  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 4.53/4.71      inference('clc', [status(thm)], ['94', '97'])).
% 4.53/4.71  thf('99', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.53/4.71      inference('demod', [status(thm)], ['5', '12', '13'])).
% 4.53/4.71  thf('100', plain,
% 4.53/4.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.53/4.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.53/4.71  thf(t7_ordinal1, axiom,
% 4.53/4.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.53/4.71  thf('101', plain,
% 4.53/4.71      (![X21 : $i, X22 : $i]:
% 4.53/4.71         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 4.53/4.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.53/4.71  thf('102', plain,
% 4.53/4.71      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 4.53/4.71      inference('sup-', [status(thm)], ['100', '101'])).
% 4.53/4.71  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.53/4.71      inference('sup-', [status(thm)], ['99', '102'])).
% 4.53/4.71  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 4.53/4.71      inference('demod', [status(thm)], ['65', '98', '103'])).
% 4.53/4.71  thf('105', plain, ((v1_xboole_0 @ sk_C_1)),
% 4.53/4.71      inference('sup-', [status(thm)], ['60', '104'])).
% 4.53/4.71  thf('106', plain, ($false), inference('demod', [status(thm)], ['59', '105'])).
% 4.53/4.71  
% 4.53/4.71  % SZS output end Refutation
% 4.53/4.71  
% 4.53/4.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
