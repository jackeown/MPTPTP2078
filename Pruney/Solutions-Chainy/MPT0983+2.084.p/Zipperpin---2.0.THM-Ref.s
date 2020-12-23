%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PzjsYkjCKj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:14 EST 2020

% Result     : Theorem 2.91s
% Output     : Refutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 337 expanded)
%              Number of leaves         :   42 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          : 1161 (6656 expanded)
%              Number of equality atoms :   32 (  78 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('2',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
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

thf('20',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
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
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

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
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != X27 )
      | ( v2_funct_2 @ X28 @ X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    inference(split,[status(esa)],['9'])).

thf('46',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('48',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('70',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

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
    inference(split,[status(esa)],['9'])).

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
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PzjsYkjCKj
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:29:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.91/3.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.91/3.10  % Solved by: fo/fo7.sh
% 2.91/3.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.91/3.10  % done 3040 iterations in 2.656s
% 2.91/3.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.91/3.10  % SZS output start Refutation
% 2.91/3.10  thf(sk_C_type, type, sk_C: $i).
% 2.91/3.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.91/3.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.91/3.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.91/3.10  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.91/3.10  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.91/3.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.91/3.10  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.91/3.10  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.91/3.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.91/3.10  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.91/3.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.91/3.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.91/3.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.91/3.10  thf(sk_A_type, type, sk_A: $i).
% 2.91/3.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.91/3.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.91/3.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.91/3.10  thf(sk_D_type, type, sk_D: $i).
% 2.91/3.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.91/3.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.91/3.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.91/3.10  thf(sk_B_type, type, sk_B: $i > $i).
% 2.91/3.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.91/3.10  thf(d1_xboole_0, axiom,
% 2.91/3.10    (![A:$i]:
% 2.91/3.10     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.91/3.10  thf('0', plain,
% 2.91/3.10      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.91/3.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.91/3.10  thf(fc3_zfmisc_1, axiom,
% 2.91/3.10    (![A:$i,B:$i]:
% 2.91/3.10     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.91/3.10  thf('1', plain,
% 2.91/3.10      (![X5 : $i, X6 : $i]:
% 2.91/3.10         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 2.91/3.10      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 2.91/3.10  thf(t29_relset_1, axiom,
% 2.91/3.10    (![A:$i]:
% 2.91/3.10     ( m1_subset_1 @
% 2.91/3.10       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.91/3.10  thf('2', plain,
% 2.91/3.10      (![X26 : $i]:
% 2.91/3.10         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 2.91/3.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 2.91/3.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.91/3.10  thf(t5_subset, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.91/3.10          ( v1_xboole_0 @ C ) ) ))).
% 2.91/3.10  thf('3', plain,
% 2.91/3.10      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.91/3.10         (~ (r2_hidden @ X9 @ X10)
% 2.91/3.10          | ~ (v1_xboole_0 @ X11)
% 2.91/3.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.91/3.10      inference('cnf', [status(esa)], [t5_subset])).
% 2.91/3.10  thf('4', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.91/3.10          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.91/3.10      inference('sup-', [status(thm)], ['2', '3'])).
% 2.91/3.10  thf('5', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 2.91/3.10      inference('sup-', [status(thm)], ['1', '4'])).
% 2.91/3.10  thf('6', plain,
% 2.91/3.10      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.91/3.10      inference('sup-', [status(thm)], ['0', '5'])).
% 2.91/3.10  thf(t8_boole, axiom,
% 2.91/3.10    (![A:$i,B:$i]:
% 2.91/3.10     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.91/3.10  thf('7', plain,
% 2.91/3.10      (![X3 : $i, X4 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 2.91/3.10      inference('cnf', [status(esa)], [t8_boole])).
% 2.91/3.10  thf('8', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ X0)
% 2.91/3.10          | ((k6_relat_1 @ X0) = (X1))
% 2.91/3.10          | ~ (v1_xboole_0 @ X1))),
% 2.91/3.10      inference('sup-', [status(thm)], ['6', '7'])).
% 2.91/3.10  thf(t29_funct_2, conjecture,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.91/3.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.91/3.10       ( ![D:$i]:
% 2.91/3.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.91/3.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.91/3.10           ( ( r2_relset_1 @
% 2.91/3.10               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.91/3.10               ( k6_partfun1 @ A ) ) =>
% 2.91/3.10             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.91/3.10  thf(zf_stmt_0, negated_conjecture,
% 2.91/3.10    (~( ![A:$i,B:$i,C:$i]:
% 2.91/3.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.91/3.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.91/3.10          ( ![D:$i]:
% 2.91/3.10            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.91/3.10                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.91/3.10              ( ( r2_relset_1 @
% 2.91/3.10                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.91/3.10                  ( k6_partfun1 @ A ) ) =>
% 2.91/3.10                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.91/3.10    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.91/3.10  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.91/3.10      inference('split', [status(esa)], ['9'])).
% 2.91/3.10  thf('11', plain,
% 2.91/3.10      ((![X0 : $i]:
% 2.91/3.10          (~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 2.91/3.10           | ~ (v1_xboole_0 @ sk_C)
% 2.91/3.10           | ~ (v1_xboole_0 @ X0)))
% 2.91/3.10         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.91/3.10      inference('sup-', [status(thm)], ['8', '10'])).
% 2.91/3.10  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.91/3.10  thf('12', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 2.91/3.10      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.91/3.10  thf('13', plain,
% 2.91/3.10      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 2.91/3.10         <= (~ ((v2_funct_1 @ sk_C)))),
% 2.91/3.10      inference('demod', [status(thm)], ['11', '12'])).
% 2.91/3.10  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.91/3.10      inference('condensation', [status(thm)], ['13'])).
% 2.91/3.10  thf('15', plain,
% 2.91/3.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.91/3.10        (k6_partfun1 @ sk_A))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(redefinition_k6_partfun1, axiom,
% 2.91/3.10    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.91/3.10  thf('16', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.91/3.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.91/3.10  thf('17', plain,
% 2.91/3.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.91/3.10        (k6_relat_1 @ sk_A))),
% 2.91/3.10      inference('demod', [status(thm)], ['15', '16'])).
% 2.91/3.10  thf('18', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(t24_funct_2, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.91/3.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.91/3.10       ( ![D:$i]:
% 2.91/3.10         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.91/3.10             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.91/3.10           ( ( r2_relset_1 @
% 2.91/3.10               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.91/3.10               ( k6_partfun1 @ B ) ) =>
% 2.91/3.10             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.91/3.10  thf('19', plain,
% 2.91/3.10      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X36)
% 2.91/3.10          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.91/3.10          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.91/3.10          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 2.91/3.10               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 2.91/3.10               (k6_partfun1 @ X37))
% 2.91/3.10          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 2.91/3.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 2.91/3.10          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 2.91/3.10          | ~ (v1_funct_1 @ X39))),
% 2.91/3.10      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.91/3.10  thf('20', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 2.91/3.10      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.91/3.10  thf('21', plain,
% 2.91/3.10      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X36)
% 2.91/3.10          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.91/3.10          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.91/3.10          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 2.91/3.10               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 2.91/3.10               (k6_relat_1 @ X37))
% 2.91/3.10          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 2.91/3.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 2.91/3.10          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 2.91/3.10          | ~ (v1_funct_1 @ X39))),
% 2.91/3.10      inference('demod', [status(thm)], ['19', '20'])).
% 2.91/3.10  thf('22', plain,
% 2.91/3.10      (![X0 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X0)
% 2.91/3.10          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.91/3.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.91/3.10          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.91/3.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.91/3.10               (k6_relat_1 @ sk_A))
% 2.91/3.10          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.91/3.10          | ~ (v1_funct_1 @ sk_C))),
% 2.91/3.10      inference('sup-', [status(thm)], ['18', '21'])).
% 2.91/3.10  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('25', plain,
% 2.91/3.10      (![X0 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X0)
% 2.91/3.10          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 2.91/3.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.91/3.10          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 2.91/3.10          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 2.91/3.10               (k6_relat_1 @ sk_A)))),
% 2.91/3.10      inference('demod', [status(thm)], ['22', '23', '24'])).
% 2.91/3.10  thf('26', plain,
% 2.91/3.10      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 2.91/3.10        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 2.91/3.10        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.91/3.10        | ~ (v1_funct_1 @ sk_D))),
% 2.91/3.10      inference('sup-', [status(thm)], ['17', '25'])).
% 2.91/3.10  thf('27', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(redefinition_k2_relset_1, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.91/3.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.91/3.10  thf('28', plain,
% 2.91/3.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.91/3.10         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.91/3.10          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.91/3.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.91/3.10  thf('29', plain,
% 2.91/3.10      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.91/3.10      inference('sup-', [status(thm)], ['27', '28'])).
% 2.91/3.10  thf('30', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('33', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.91/3.10      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 2.91/3.10  thf(d3_funct_2, axiom,
% 2.91/3.10    (![A:$i,B:$i]:
% 2.91/3.10     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.91/3.10       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.91/3.10  thf('34', plain,
% 2.91/3.10      (![X27 : $i, X28 : $i]:
% 2.91/3.10         (((k2_relat_1 @ X28) != (X27))
% 2.91/3.10          | (v2_funct_2 @ X28 @ X27)
% 2.91/3.10          | ~ (v5_relat_1 @ X28 @ X27)
% 2.91/3.10          | ~ (v1_relat_1 @ X28))),
% 2.91/3.10      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.91/3.10  thf('35', plain,
% 2.91/3.10      (![X28 : $i]:
% 2.91/3.10         (~ (v1_relat_1 @ X28)
% 2.91/3.10          | ~ (v5_relat_1 @ X28 @ (k2_relat_1 @ X28))
% 2.91/3.10          | (v2_funct_2 @ X28 @ (k2_relat_1 @ X28)))),
% 2.91/3.10      inference('simplify', [status(thm)], ['34'])).
% 2.91/3.10  thf('36', plain,
% 2.91/3.10      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.91/3.10        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.91/3.10        | ~ (v1_relat_1 @ sk_D))),
% 2.91/3.10      inference('sup-', [status(thm)], ['33', '35'])).
% 2.91/3.10  thf('37', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(cc2_relset_1, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.91/3.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.91/3.10  thf('38', plain,
% 2.91/3.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.91/3.10         ((v5_relat_1 @ X16 @ X18)
% 2.91/3.10          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 2.91/3.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.91/3.10  thf('39', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.91/3.10      inference('sup-', [status(thm)], ['37', '38'])).
% 2.91/3.10  thf('40', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.91/3.10      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 2.91/3.10  thf('41', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(cc1_relset_1, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i]:
% 2.91/3.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.91/3.10       ( v1_relat_1 @ C ) ))).
% 2.91/3.10  thf('42', plain,
% 2.91/3.10      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.91/3.10         ((v1_relat_1 @ X13)
% 2.91/3.10          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 2.91/3.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.91/3.10  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 2.91/3.10      inference('sup-', [status(thm)], ['41', '42'])).
% 2.91/3.10  thf('44', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.91/3.10      inference('demod', [status(thm)], ['36', '39', '40', '43'])).
% 2.91/3.10  thf('45', plain,
% 2.91/3.10      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.91/3.10      inference('split', [status(esa)], ['9'])).
% 2.91/3.10  thf('46', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.91/3.10      inference('sup-', [status(thm)], ['44', '45'])).
% 2.91/3.10  thf('47', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.91/3.10      inference('split', [status(esa)], ['9'])).
% 2.91/3.10  thf('48', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.91/3.10      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 2.91/3.10  thf('49', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.91/3.10      inference('simpl_trail', [status(thm)], ['14', '48'])).
% 2.91/3.10  thf('50', plain,
% 2.91/3.10      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.91/3.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.91/3.10  thf(fc4_zfmisc_1, axiom,
% 2.91/3.10    (![A:$i,B:$i]:
% 2.91/3.10     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.91/3.10  thf('51', plain,
% 2.91/3.10      (![X7 : $i, X8 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 2.91/3.10      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.91/3.10  thf('52', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('53', plain,
% 2.91/3.10      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.91/3.10         (~ (r2_hidden @ X9 @ X10)
% 2.91/3.10          | ~ (v1_xboole_0 @ X11)
% 2.91/3.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.91/3.10      inference('cnf', [status(esa)], [t5_subset])).
% 2.91/3.10  thf('54', plain,
% 2.91/3.10      (![X0 : $i]:
% 2.91/3.10         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.91/3.10          | ~ (r2_hidden @ X0 @ sk_C))),
% 2.91/3.10      inference('sup-', [status(thm)], ['52', '53'])).
% 2.91/3.10  thf('55', plain,
% 2.91/3.10      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 2.91/3.10      inference('sup-', [status(thm)], ['51', '54'])).
% 2.91/3.10  thf('56', plain,
% 2.91/3.10      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.91/3.10        (k6_relat_1 @ sk_A))),
% 2.91/3.10      inference('demod', [status(thm)], ['15', '16'])).
% 2.91/3.10  thf('57', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('58', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(dt_k1_partfun1, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.91/3.10     ( ( ( v1_funct_1 @ E ) & 
% 2.91/3.10         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.91/3.10         ( v1_funct_1 @ F ) & 
% 2.91/3.10         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.91/3.10       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.91/3.10         ( m1_subset_1 @
% 2.91/3.10           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.91/3.10           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.91/3.10  thf('59', plain,
% 2.91/3.10      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 2.91/3.10         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.91/3.10          | ~ (v1_funct_1 @ X29)
% 2.91/3.10          | ~ (v1_funct_1 @ X32)
% 2.91/3.10          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.91/3.10          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 2.91/3.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 2.91/3.10      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.91/3.10  thf('60', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.91/3.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.91/3.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.91/3.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.91/3.10          | ~ (v1_funct_1 @ X1)
% 2.91/3.10          | ~ (v1_funct_1 @ sk_C))),
% 2.91/3.10      inference('sup-', [status(thm)], ['58', '59'])).
% 2.91/3.10  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('62', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.91/3.10         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 2.91/3.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.91/3.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.91/3.10          | ~ (v1_funct_1 @ X1))),
% 2.91/3.10      inference('demod', [status(thm)], ['60', '61'])).
% 2.91/3.10  thf('63', plain,
% 2.91/3.10      ((~ (v1_funct_1 @ sk_D)
% 2.91/3.10        | (m1_subset_1 @ 
% 2.91/3.10           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.91/3.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.91/3.10      inference('sup-', [status(thm)], ['57', '62'])).
% 2.91/3.10  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('65', plain,
% 2.91/3.10      ((m1_subset_1 @ 
% 2.91/3.10        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 2.91/3.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.91/3.10      inference('demod', [status(thm)], ['63', '64'])).
% 2.91/3.10  thf(redefinition_r2_relset_1, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i,D:$i]:
% 2.91/3.10     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.91/3.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.91/3.10       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.91/3.10  thf('66', plain,
% 2.91/3.10      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.91/3.10         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.91/3.10          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.91/3.10          | ((X22) = (X25))
% 2.91/3.10          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 2.91/3.10      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.91/3.10  thf('67', plain,
% 2.91/3.10      (![X0 : $i]:
% 2.91/3.10         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.91/3.10             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 2.91/3.10          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 2.91/3.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.91/3.10      inference('sup-', [status(thm)], ['65', '66'])).
% 2.91/3.10  thf('68', plain,
% 2.91/3.10      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.91/3.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.91/3.10        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.91/3.10            = (k6_relat_1 @ sk_A)))),
% 2.91/3.10      inference('sup-', [status(thm)], ['56', '67'])).
% 2.91/3.10  thf('69', plain,
% 2.91/3.10      (![X26 : $i]:
% 2.91/3.10         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 2.91/3.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 2.91/3.10      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.91/3.10  thf('70', plain,
% 2.91/3.10      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 2.91/3.10         = (k6_relat_1 @ sk_A))),
% 2.91/3.10      inference('demod', [status(thm)], ['68', '69'])).
% 2.91/3.10  thf('71', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf(t26_funct_2, axiom,
% 2.91/3.10    (![A:$i,B:$i,C:$i,D:$i]:
% 2.91/3.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.91/3.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.91/3.10       ( ![E:$i]:
% 2.91/3.10         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.91/3.10             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.91/3.10           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.91/3.10             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.91/3.10               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.91/3.10  thf('72', plain,
% 2.91/3.10      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X40)
% 2.91/3.10          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 2.91/3.10          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.91/3.10          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 2.91/3.10          | (v2_funct_1 @ X44)
% 2.91/3.10          | ((X42) = (k1_xboole_0))
% 2.91/3.10          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 2.91/3.10          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 2.91/3.10          | ~ (v1_funct_1 @ X44))),
% 2.91/3.10      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.91/3.10  thf('73', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X0)
% 2.91/3.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.91/3.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.91/3.10          | ((sk_A) = (k1_xboole_0))
% 2.91/3.10          | (v2_funct_1 @ X0)
% 2.91/3.10          | ~ (v2_funct_1 @ 
% 2.91/3.10               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 2.91/3.10          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.91/3.10          | ~ (v1_funct_1 @ sk_D))),
% 2.91/3.10      inference('sup-', [status(thm)], ['71', '72'])).
% 2.91/3.10  thf('74', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('76', plain,
% 2.91/3.10      (![X0 : $i, X1 : $i]:
% 2.91/3.10         (~ (v1_funct_1 @ X0)
% 2.91/3.10          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.91/3.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.91/3.10          | ((sk_A) = (k1_xboole_0))
% 2.91/3.10          | (v2_funct_1 @ X0)
% 2.91/3.10          | ~ (v2_funct_1 @ 
% 2.91/3.10               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 2.91/3.10      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.91/3.10  thf('77', plain,
% 2.91/3.10      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.91/3.10        | (v2_funct_1 @ sk_C)
% 2.91/3.10        | ((sk_A) = (k1_xboole_0))
% 2.91/3.10        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.91/3.10        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 2.91/3.10        | ~ (v1_funct_1 @ sk_C))),
% 2.91/3.10      inference('sup-', [status(thm)], ['70', '76'])).
% 2.91/3.10  thf('78', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 2.91/3.10      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.91/3.10  thf('79', plain,
% 2.91/3.10      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('80', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 2.91/3.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.91/3.10  thf('82', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.91/3.10      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 2.91/3.10  thf('83', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.91/3.10      inference('split', [status(esa)], ['9'])).
% 2.91/3.10  thf('84', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.91/3.10      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 2.91/3.10  thf('85', plain, (~ (v2_funct_1 @ sk_C)),
% 2.91/3.10      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 2.91/3.10  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 2.91/3.10      inference('clc', [status(thm)], ['82', '85'])).
% 2.91/3.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.91/3.10  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.91/3.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.91/3.10  thf('88', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 2.91/3.10      inference('demod', [status(thm)], ['55', '86', '87'])).
% 2.91/3.10  thf('89', plain, ((v1_xboole_0 @ sk_C)),
% 2.91/3.10      inference('sup-', [status(thm)], ['50', '88'])).
% 2.91/3.10  thf('90', plain, ($false), inference('demod', [status(thm)], ['49', '89'])).
% 2.91/3.10  
% 2.91/3.10  % SZS output end Refutation
% 2.91/3.10  
% 2.91/3.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
