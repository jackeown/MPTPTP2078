%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SddiQe8TdV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:14 EST 2020

% Result     : Theorem 2.77s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 322 expanded)
%              Number of leaves         :   41 ( 111 expanded)
%              Depth                    :   15
%              Number of atoms          : 1114 (6404 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('2',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('15',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['17'])).

thf('19',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ X27 )
       != X26 )
      | ( v2_funct_2 @ X27 @ X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
      | ( v2_funct_2 @ X27 @ ( k2_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('39',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['36','39','40','43'])).

thf('45',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('46',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('48',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['18','48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39 ) )
      | ( v2_funct_1 @ X43 )
      | ( X41 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X40 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('84',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('85',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['82','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['55','86','87'])).

thf('89',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['50','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['49','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SddiQe8TdV
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:52:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.77/2.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.77/2.97  % Solved by: fo/fo7.sh
% 2.77/2.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.77/2.97  % done 2186 iterations in 2.522s
% 2.77/2.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.77/2.97  % SZS output start Refutation
% 2.77/2.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.77/2.97  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.77/2.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.77/2.97  thf(sk_B_type, type, sk_B: $i > $i).
% 2.77/2.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.77/2.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.77/2.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.77/2.97  thf(sk_A_type, type, sk_A: $i).
% 2.77/2.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.77/2.97  thf(sk_C_type, type, sk_C: $i).
% 2.77/2.97  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.77/2.97  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.77/2.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.77/2.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.77/2.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.77/2.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.77/2.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.77/2.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.77/2.97  thf(sk_D_type, type, sk_D: $i).
% 2.77/2.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.77/2.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.77/2.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.77/2.97  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.77/2.97  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.77/2.97  thf(d1_xboole_0, axiom,
% 2.77/2.97    (![A:$i]:
% 2.77/2.97     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.77/2.97  thf('0', plain,
% 2.77/2.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.77/2.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.77/2.97  thf(fc4_zfmisc_1, axiom,
% 2.77/2.97    (![A:$i,B:$i]:
% 2.77/2.97     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.77/2.97  thf('1', plain,
% 2.77/2.97      (![X5 : $i, X6 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 2.77/2.97      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.77/2.97  thf(t29_relset_1, axiom,
% 2.77/2.97    (![A:$i]:
% 2.77/2.97     ( m1_subset_1 @
% 2.77/2.97       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.77/2.97  thf('2', plain,
% 2.77/2.97      (![X25 : $i]:
% 2.77/2.97         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 2.77/2.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 2.77/2.97      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.77/2.97  thf(redefinition_k6_partfun1, axiom,
% 2.77/2.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.77/2.97  thf('3', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.77/2.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.77/2.97  thf('4', plain,
% 2.77/2.97      (![X25 : $i]:
% 2.77/2.97         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 2.77/2.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 2.77/2.97      inference('demod', [status(thm)], ['2', '3'])).
% 2.77/2.97  thf(t5_subset, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.77/2.97          ( v1_xboole_0 @ C ) ) ))).
% 2.77/2.97  thf('5', plain,
% 2.77/2.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.77/2.97         (~ (r2_hidden @ X7 @ X8)
% 2.77/2.97          | ~ (v1_xboole_0 @ X9)
% 2.77/2.97          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.77/2.97      inference('cnf', [status(esa)], [t5_subset])).
% 2.77/2.97  thf('6', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.77/2.97          | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 2.77/2.97      inference('sup-', [status(thm)], ['4', '5'])).
% 2.77/2.97  thf('7', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 2.77/2.97      inference('sup-', [status(thm)], ['1', '6'])).
% 2.77/2.97  thf('8', plain,
% 2.77/2.97      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.77/2.97      inference('sup-', [status(thm)], ['0', '7'])).
% 2.77/2.97  thf(t8_boole, axiom,
% 2.77/2.97    (![A:$i,B:$i]:
% 2.77/2.97     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.77/2.97  thf('9', plain,
% 2.77/2.97      (![X3 : $i, X4 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 2.77/2.97      inference('cnf', [status(esa)], [t8_boole])).
% 2.77/2.97  thf('10', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ X0)
% 2.77/2.97          | ((k6_partfun1 @ X0) = (X1))
% 2.77/2.97          | ~ (v1_xboole_0 @ X1))),
% 2.77/2.97      inference('sup-', [status(thm)], ['8', '9'])).
% 2.77/2.97  thf(t29_funct_2, conjecture,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/2.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/2.97       ( ![D:$i]:
% 2.77/2.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/2.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/2.97           ( ( r2_relset_1 @
% 2.77/2.97               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.77/2.97               ( k6_partfun1 @ A ) ) =>
% 2.77/2.97             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.77/2.97  thf(zf_stmt_0, negated_conjecture,
% 2.77/2.97    (~( ![A:$i,B:$i,C:$i]:
% 2.77/2.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/2.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/2.97          ( ![D:$i]:
% 2.77/2.97            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/2.97                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/2.97              ( ( r2_relset_1 @
% 2.77/2.97                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.77/2.97                  ( k6_partfun1 @ A ) ) =>
% 2.77/2.97                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.77/2.97    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.77/2.97  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/2.97      inference('split', [status(esa)], ['11'])).
% 2.77/2.97  thf('13', plain,
% 2.77/2.97      ((![X0 : $i]:
% 2.77/2.97          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 2.77/2.97           | ~ (v1_xboole_0 @ sk_C)
% 2.77/2.97           | ~ (v1_xboole_0 @ X0)))
% 2.77/2.97         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/2.97      inference('sup-', [status(thm)], ['10', '12'])).
% 2.77/2.97  thf(fc4_funct_1, axiom,
% 2.77/2.97    (![A:$i]:
% 2.77/2.97     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.77/2.97       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.77/2.97  thf('14', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 2.77/2.97      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.77/2.97  thf('15', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 2.77/2.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.77/2.97  thf('16', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 2.77/2.97      inference('demod', [status(thm)], ['14', '15'])).
% 2.77/2.97  thf('17', plain,
% 2.77/2.97      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 2.77/2.97         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/2.97      inference('demod', [status(thm)], ['13', '16'])).
% 2.77/2.97  thf('18', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/2.97      inference('condensation', [status(thm)], ['17'])).
% 2.77/2.97  thf('19', plain,
% 2.77/2.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/2.97        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.77/2.97        (k6_partfun1 @ sk_A))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('20', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(t24_funct_2, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.77/2.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/2.97       ( ![D:$i]:
% 2.77/2.97         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.77/2.97             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.77/2.97           ( ( r2_relset_1 @
% 2.77/2.97               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.77/2.97               ( k6_partfun1 @ B ) ) =>
% 2.77/2.97             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.77/2.97  thf('21', plain,
% 2.77/2.97      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X35)
% 2.77/2.97          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 2.77/2.97          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 2.77/2.97          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 2.77/2.97               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 2.77/2.97               (k6_partfun1 @ X36))
% 2.77/2.97          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 2.77/2.97          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 2.77/2.97          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 2.77/2.97          | ~ (v1_funct_1 @ X38))),
% 2.77/2.97      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.77/2.97  thf('22', plain,
% 2.77/2.97      (![X0 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X0)
% 2.77/2.97          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.77/2.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.77/2.97          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.77/2.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/2.97               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.77/2.97               (k6_partfun1 @ sk_A))
% 2.77/2.97          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.77/2.97          | ~ (v1_funct_1 @ sk_C))),
% 2.77/2.97      inference('sup-', [status(thm)], ['20', '21'])).
% 2.77/2.97  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('25', plain,
% 2.77/2.97      (![X0 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X0)
% 2.77/2.97          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.77/2.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.77/2.97          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.77/2.97          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/2.97               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.77/2.97               (k6_partfun1 @ sk_A)))),
% 2.77/2.97      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.77/2.97  thf('26', plain,
% 2.77/2.97      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 2.77/2.97        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.77/2.97        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.77/2.97        | ~ (v1_funct_1 @ sk_D))),
% 2.77/2.97      inference('sup-', [status(thm)], ['19', '25'])).
% 2.77/2.97  thf('27', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(redefinition_k2_relset_1, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/2.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.77/2.97  thf('28', plain,
% 2.77/2.97      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.77/2.97         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.77/2.97          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.77/2.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.77/2.97  thf('29', plain,
% 2.77/2.97      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.77/2.97      inference('sup-', [status(thm)], ['27', '28'])).
% 2.77/2.97  thf('30', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('33', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.77/2.97      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 2.77/2.97  thf(d3_funct_2, axiom,
% 2.77/2.97    (![A:$i,B:$i]:
% 2.77/2.97     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.77/2.97       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.77/2.97  thf('34', plain,
% 2.77/2.97      (![X26 : $i, X27 : $i]:
% 2.77/2.97         (((k2_relat_1 @ X27) != (X26))
% 2.77/2.97          | (v2_funct_2 @ X27 @ X26)
% 2.77/2.97          | ~ (v5_relat_1 @ X27 @ X26)
% 2.77/2.97          | ~ (v1_relat_1 @ X27))),
% 2.77/2.97      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.77/2.97  thf('35', plain,
% 2.77/2.97      (![X27 : $i]:
% 2.77/2.97         (~ (v1_relat_1 @ X27)
% 2.77/2.97          | ~ (v5_relat_1 @ X27 @ (k2_relat_1 @ X27))
% 2.77/2.97          | (v2_funct_2 @ X27 @ (k2_relat_1 @ X27)))),
% 2.77/2.97      inference('simplify', [status(thm)], ['34'])).
% 2.77/2.97  thf('36', plain,
% 2.77/2.97      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.77/2.97        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.77/2.97        | ~ (v1_relat_1 @ sk_D))),
% 2.77/2.97      inference('sup-', [status(thm)], ['33', '35'])).
% 2.77/2.97  thf('37', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(cc2_relset_1, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/2.97       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.77/2.97  thf('38', plain,
% 2.77/2.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.77/2.97         ((v5_relat_1 @ X15 @ X17)
% 2.77/2.97          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.77/2.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.77/2.97  thf('39', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.77/2.97      inference('sup-', [status(thm)], ['37', '38'])).
% 2.77/2.97  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.77/2.97      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 2.77/2.97  thf('41', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(cc1_relset_1, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i]:
% 2.77/2.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.77/2.97       ( v1_relat_1 @ C ) ))).
% 2.77/2.97  thf('42', plain,
% 2.77/2.97      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.77/2.97         ((v1_relat_1 @ X12)
% 2.77/2.97          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.77/2.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.77/2.97  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 2.77/2.97      inference('sup-', [status(thm)], ['41', '42'])).
% 2.77/2.97  thf('44', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.77/2.97      inference('demod', [status(thm)], ['36', '39', '40', '43'])).
% 2.77/2.97  thf('45', plain,
% 2.77/2.97      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.77/2.97      inference('split', [status(esa)], ['11'])).
% 2.77/2.97  thf('46', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.77/2.97      inference('sup-', [status(thm)], ['44', '45'])).
% 2.77/2.97  thf('47', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.77/2.97      inference('split', [status(esa)], ['11'])).
% 2.77/2.97  thf('48', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.77/2.97      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 2.77/2.97  thf('49', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.77/2.97      inference('simpl_trail', [status(thm)], ['18', '48'])).
% 2.77/2.97  thf('50', plain,
% 2.77/2.97      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.77/2.97      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.77/2.97  thf('51', plain,
% 2.77/2.97      (![X5 : $i, X6 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 2.77/2.97      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.77/2.97  thf('52', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('53', plain,
% 2.77/2.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.77/2.97         (~ (r2_hidden @ X7 @ X8)
% 2.77/2.97          | ~ (v1_xboole_0 @ X9)
% 2.77/2.97          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.77/2.97      inference('cnf', [status(esa)], [t5_subset])).
% 2.77/2.97  thf('54', plain,
% 2.77/2.97      (![X0 : $i]:
% 2.77/2.97         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.77/2.97          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.77/2.97      inference('sup-', [status(thm)], ['52', '53'])).
% 2.77/2.97  thf('55', plain,
% 2.77/2.97      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 2.77/2.97      inference('sup-', [status(thm)], ['51', '54'])).
% 2.77/2.97  thf('56', plain,
% 2.77/2.97      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/2.97        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.77/2.97        (k6_partfun1 @ sk_A))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('57', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('58', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(dt_k1_partfun1, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.77/2.97     ( ( ( v1_funct_1 @ E ) & 
% 2.77/2.97         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.77/2.97         ( v1_funct_1 @ F ) & 
% 2.77/2.97         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.77/2.97       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.77/2.97         ( m1_subset_1 @
% 2.77/2.97           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.77/2.97           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.77/2.97  thf('59', plain,
% 2.77/2.97      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.77/2.97         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.77/2.97          | ~ (v1_funct_1 @ X28)
% 2.77/2.97          | ~ (v1_funct_1 @ X31)
% 2.77/2.97          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 2.77/2.97          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 2.77/2.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 2.77/2.97      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.77/2.97  thf('60', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/2.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.77/2.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.77/2.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.77/2.97          | ~ (v1_funct_1 @ X1)
% 2.77/2.97          | ~ (v1_funct_1 @ sk_C))),
% 2.77/2.97      inference('sup-', [status(thm)], ['58', '59'])).
% 2.77/2.97  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('62', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.77/2.97         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.77/2.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.77/2.97          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.77/2.97          | ~ (v1_funct_1 @ X1))),
% 2.77/2.97      inference('demod', [status(thm)], ['60', '61'])).
% 2.77/2.97  thf('63', plain,
% 2.77/2.97      ((~ (v1_funct_1 @ sk_D)
% 2.77/2.97        | (m1_subset_1 @ 
% 2.77/2.97           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.77/2.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.77/2.97      inference('sup-', [status(thm)], ['57', '62'])).
% 2.77/2.97  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('65', plain,
% 2.77/2.97      ((m1_subset_1 @ 
% 2.77/2.97        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.77/2.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.77/2.97      inference('demod', [status(thm)], ['63', '64'])).
% 2.77/2.97  thf(redefinition_r2_relset_1, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i,D:$i]:
% 2.77/2.97     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.77/2.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/2.97       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.77/2.97  thf('66', plain,
% 2.77/2.97      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.77/2.97         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.77/2.97          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.77/2.97          | ((X21) = (X24))
% 2.77/2.97          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 2.77/2.97      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.77/2.97  thf('67', plain,
% 2.77/2.97      (![X0 : $i]:
% 2.77/2.97         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.77/2.97             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 2.77/2.97          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 2.77/2.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.77/2.97      inference('sup-', [status(thm)], ['65', '66'])).
% 2.77/2.97  thf('68', plain,
% 2.77/2.97      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.77/2.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.77/2.97        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.77/2.97            = (k6_partfun1 @ sk_A)))),
% 2.77/2.97      inference('sup-', [status(thm)], ['56', '67'])).
% 2.77/2.97  thf('69', plain,
% 2.77/2.97      (![X25 : $i]:
% 2.77/2.97         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 2.77/2.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 2.77/2.97      inference('demod', [status(thm)], ['2', '3'])).
% 2.77/2.97  thf('70', plain,
% 2.77/2.97      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.77/2.97         = (k6_partfun1 @ sk_A))),
% 2.77/2.97      inference('demod', [status(thm)], ['68', '69'])).
% 2.77/2.97  thf('71', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf(t26_funct_2, axiom,
% 2.77/2.97    (![A:$i,B:$i,C:$i,D:$i]:
% 2.77/2.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.77/2.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.77/2.97       ( ![E:$i]:
% 2.77/2.97         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.77/2.97             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.77/2.97           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.77/2.97             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.77/2.97               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.77/2.97  thf('72', plain,
% 2.77/2.97      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X39)
% 2.77/2.97          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 2.77/2.97          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 2.77/2.97          | ~ (v2_funct_1 @ (k1_partfun1 @ X42 @ X40 @ X40 @ X41 @ X43 @ X39))
% 2.77/2.97          | (v2_funct_1 @ X43)
% 2.77/2.97          | ((X41) = (k1_xboole_0))
% 2.77/2.97          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X40)))
% 2.77/2.97          | ~ (v1_funct_2 @ X43 @ X42 @ X40)
% 2.77/2.97          | ~ (v1_funct_1 @ X43))),
% 2.77/2.97      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.77/2.97  thf('73', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X0)
% 2.77/2.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.77/2.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.77/2.97          | ((sk_A) = (k1_xboole_0))
% 2.77/2.97          | (v2_funct_1 @ X0)
% 2.77/2.97          | ~ (v2_funct_1 @ 
% 2.77/2.97               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 2.77/2.97          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.77/2.97          | ~ (v1_funct_1 @ sk_D))),
% 2.77/2.97      inference('sup-', [status(thm)], ['71', '72'])).
% 2.77/2.97  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('76', plain,
% 2.77/2.97      (![X0 : $i, X1 : $i]:
% 2.77/2.97         (~ (v1_funct_1 @ X0)
% 2.77/2.97          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.77/2.97          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.77/2.97          | ((sk_A) = (k1_xboole_0))
% 2.77/2.97          | (v2_funct_1 @ X0)
% 2.77/2.97          | ~ (v2_funct_1 @ 
% 2.77/2.97               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 2.77/2.97      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.77/2.97  thf('77', plain,
% 2.77/2.97      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.77/2.97        | (v2_funct_1 @ sk_C)
% 2.77/2.97        | ((sk_A) = (k1_xboole_0))
% 2.77/2.97        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.77/2.97        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.77/2.97        | ~ (v1_funct_1 @ sk_C))),
% 2.77/2.97      inference('sup-', [status(thm)], ['70', '76'])).
% 2.77/2.97  thf('78', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 2.77/2.97      inference('demod', [status(thm)], ['14', '15'])).
% 2.77/2.97  thf('79', plain,
% 2.77/2.97      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('80', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 2.77/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.77/2.97  thf('82', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.77/2.97      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 2.77/2.97  thf('83', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.77/2.97      inference('split', [status(esa)], ['11'])).
% 2.77/2.97  thf('84', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.77/2.97      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 2.77/2.97  thf('85', plain, (~ (v2_funct_1 @ sk_C)),
% 2.77/2.97      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 2.77/2.97  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 2.77/2.97      inference('clc', [status(thm)], ['82', '85'])).
% 2.77/2.97  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.77/2.97  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.77/2.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.77/2.97  thf('88', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 2.77/2.97      inference('demod', [status(thm)], ['55', '86', '87'])).
% 2.77/2.97  thf('89', plain, ((v1_xboole_0 @ sk_C)),
% 2.77/2.97      inference('sup-', [status(thm)], ['50', '88'])).
% 2.77/2.97  thf('90', plain, ($false), inference('demod', [status(thm)], ['49', '89'])).
% 2.77/2.97  
% 2.77/2.97  % SZS output end Refutation
% 2.77/2.97  
% 2.77/2.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
