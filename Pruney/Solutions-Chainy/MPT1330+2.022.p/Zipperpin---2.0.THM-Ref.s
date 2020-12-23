%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buasxS2fcd

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 310 expanded)
%              Number of leaves         :   34 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          : 1032 (4745 expanded)
%              Number of equality atoms :   91 ( 362 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( v1_partfun1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('4',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ( v1_partfun1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('20',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('26',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X39 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ( v1_partfun1 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ k1_xboole_0 @ X37 )
      | ( v1_partfun1 @ X38 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_partfun1 @ sk_C_1 @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('37',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( v1_partfun1 @ sk_C_1 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','42'])).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X35 )
      | ( ( k1_relat_1 @ X36 )
        = X35 )
      | ~ ( v4_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v4_relat_1 @ sk_C_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,
    ( ( v4_relat_1 @ sk_C_1 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('52',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('59',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('61',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
        = ( k10_relat_1 @ sk_C_1 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X24: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('64',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('77',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k10_relat_1 @ X22 @ X23 )
        = ( k10_relat_1 @ X22 @ ( k3_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('78',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('80',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['63','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('83',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62','83'])).

thf('85',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['50','84'])).

thf('86',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('87',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','87'])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','88'])).

thf('90',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k8_relset_1 @ X31 @ X32 @ X30 @ X33 )
        = ( k10_relat_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 @ X0 )
      = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('98',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','96','97'])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buasxS2fcd
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 179 iterations in 0.047s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.49  thf(d3_struct_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf(t52_tops_2, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( l1_struct_0 @ B ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                 ( m1_subset_1 @
% 0.19/0.49                   C @ 
% 0.19/0.49                   ( k1_zfmisc_1 @
% 0.19/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.49                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.49                 ( ( k8_relset_1 @
% 0.19/0.49                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.49                     ( k2_struct_0 @ B ) ) =
% 0.19/0.49                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( l1_struct_0 @ A ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( l1_struct_0 @ B ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                    ( v1_funct_2 @
% 0.19/0.49                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                    ( m1_subset_1 @
% 0.19/0.49                      C @ 
% 0.19/0.49                      ( k1_zfmisc_1 @
% 0.19/0.49                        ( k2_zfmisc_1 @
% 0.19/0.49                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.49                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.49                    ( ( k8_relset_1 @
% 0.19/0.49                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.49                        ( k2_struct_0 @ B ) ) =
% 0.19/0.49                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t132_funct_2, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.49           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.49           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.49         (((X37) = (k1_xboole_0))
% 0.19/0.49          | ~ (v1_funct_1 @ X38)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.19/0.49          | (v1_partfun1 @ X38 @ X39)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.19/0.49          | ~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.19/0.49          | ~ (v1_funct_1 @ X38))),
% 0.19/0.49      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.49         (~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.19/0.49          | (v1_partfun1 @ X38 @ X39)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.19/0.49          | ~ (v1_funct_1 @ X38)
% 0.19/0.49          | ((X37) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | ~ (v1_funct_1 @ sk_C_1)
% 0.19/0.49        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.19/0.49  thf('6', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.19/0.49  thf(d4_partfun1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.49       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X35 : $i, X36 : $i]:
% 0.19/0.49         (~ (v1_partfun1 @ X36 @ X35)
% 0.19/0.49          | ((k1_relat_1 @ X36) = (X35))
% 0.19/0.49          | ~ (v4_relat_1 @ X36 @ X35)
% 0.19/0.49          | ~ (v1_relat_1 @ X36))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.19/0.49          | (v1_relat_1 @ X16)
% 0.19/0.49          | ~ (v1_relat_1 @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ 
% 0.19/0.49           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.19/0.49        | (v1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf(fc6_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.49  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.49         ((v4_relat_1 @ X27 @ X28)
% 0.19/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('18', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B_1)
% 0.19/0.49        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['1', '19'])).
% 0.19/0.49  thf('21', plain, ((l1_struct_0 @ sk_B_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.49        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.19/0.49        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 0.19/0.49         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['25', '30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.49         (((X39) != (k1_xboole_0))
% 0.19/0.49          | ~ (v1_funct_1 @ X38)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.19/0.49          | (v1_partfun1 @ X38 @ X39)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.19/0.49          | ~ (v1_funct_2 @ X38 @ X39 @ X37)
% 0.19/0.49          | ~ (v1_funct_1 @ X38))),
% 0.19/0.49      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X37 : $i, X38 : $i]:
% 0.19/0.49         (~ (v1_funct_2 @ X38 @ k1_xboole_0 @ X37)
% 0.19/0.49          | (v1_partfun1 @ X38 @ k1_xboole_0)
% 0.19/0.49          | ~ (m1_subset_1 @ X38 @ 
% 0.19/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X37)))
% 0.19/0.49          | ~ (v1_funct_1 @ X38))),
% 0.19/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((~ (v1_funct_1 @ sk_C_1)
% 0.19/0.49         | (v1_partfun1 @ sk_C_1 @ k1_xboole_0)
% 0.19/0.49         | ~ (v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['31', '33'])).
% 0.19/0.49  thf('35', plain, ((v1_funct_1 @ sk_C_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (((v1_funct_2 @ sk_C_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['36', '41'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (((v1_partfun1 @ sk_C_1 @ k1_xboole_0))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['34', '35', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X35 : $i, X36 : $i]:
% 0.19/0.49         (~ (v1_partfun1 @ X36 @ X35)
% 0.19/0.49          | ((k1_relat_1 @ X36) = (X35))
% 0.19/0.49          | ~ (v4_relat_1 @ X36 @ X35)
% 0.19/0.49          | ~ (v1_relat_1 @ X36))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (((~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49         | ~ (v4_relat_1 @ sk_C_1 @ k1_xboole_0)
% 0.19/0.49         | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['25', '30'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.49         ((v4_relat_1 @ X27 @ X28)
% 0.19/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (((v4_relat_1 @ sk_C_1 @ k1_xboole_0))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49          sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.49  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.19/0.49          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '56'])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C_1 @ 
% 0.19/0.49          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['25', '30'])).
% 0.19/0.49  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.19/0.49          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C_1 @ X0)
% 0.19/0.49            = (k10_relat_1 @ sk_C_1 @ X0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.49  thf(t169_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      (![X24 : $i]:
% 0.19/0.49         (((k10_relat_1 @ X24 @ (k2_relat_1 @ X24)) = (k1_relat_1 @ X24))
% 0.19/0.49          | ~ (v1_relat_1 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      (![X40 : $i]:
% 0.19/0.49         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.49  thf('65', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('66', plain,
% 0.19/0.49      (((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['64', '65'])).
% 0.19/0.49  thf('67', plain, ((l1_struct_0 @ sk_B_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('68', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.19/0.49  thf('69', plain,
% 0.19/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.49         ((v5_relat_1 @ X27 @ X29)
% 0.19/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('70', plain, ((v5_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.49  thf(d19_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.49  thf('71', plain,
% 0.19/0.49      (![X18 : $i, X19 : $i]:
% 0.19/0.49         (~ (v5_relat_1 @ X18 @ X19)
% 0.19/0.49          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.19/0.49          | ~ (v1_relat_1 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.49  thf('72', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49        | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.49  thf('73', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('74', plain,
% 0.19/0.49      ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('75', plain,
% 0.19/0.49      (![X4 : $i, X5 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('76', plain,
% 0.19/0.49      (((k3_xboole_0 @ (k2_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1))
% 0.19/0.49         = (k2_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.49  thf(t168_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( k10_relat_1 @ B @ A ) =
% 0.19/0.49         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.19/0.49  thf('77', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (((k10_relat_1 @ X22 @ X23)
% 0.19/0.49            = (k10_relat_1 @ X22 @ (k3_xboole_0 @ (k2_relat_1 @ X22) @ X23)))
% 0.19/0.49          | ~ (v1_relat_1 @ X22))),
% 0.19/0.49      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.19/0.49  thf('78', plain,
% 0.19/0.49      ((((k10_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1))
% 0.19/0.49          = (k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['76', '77'])).
% 0.19/0.49  thf('79', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('80', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1))
% 0.19/0.49         = (k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['78', '79'])).
% 0.19/0.49  thf('81', plain,
% 0.19/0.49      ((((k10_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1))
% 0.19/0.49          = (k1_relat_1 @ sk_C_1))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['63', '80'])).
% 0.19/0.49  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('83', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['81', '82'])).
% 0.19/0.49  thf('84', plain,
% 0.19/0.49      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0)))
% 0.19/0.49         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.49      inference('demod', [status(thm)], ['59', '62', '83'])).
% 0.19/0.49  thf('85', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['50', '84'])).
% 0.19/0.49  thf('86', plain,
% 0.19/0.49      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 0.19/0.49       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('split', [status(esa)], ['23'])).
% 0.19/0.49  thf('87', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 0.19/0.49  thf('88', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['24', '87'])).
% 0.19/0.49  thf('89', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['22', '88'])).
% 0.19/0.49  thf('90', plain,
% 0.19/0.49      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['0', '89'])).
% 0.19/0.49  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('92', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['90', '91'])).
% 0.19/0.49  thf('93', plain,
% 0.19/0.49      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49         sk_C_1 @ (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('94', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('95', plain,
% 0.19/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.19/0.49          | ((k8_relset_1 @ X31 @ X32 @ X30 @ X33) = (k10_relat_1 @ X30 @ X33)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.49  thf('96', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49           sk_C_1 @ X0) = (k10_relat_1 @ sk_C_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.49  thf('97', plain,
% 0.19/0.49      (((k10_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['81', '82'])).
% 0.19/0.49  thf('98', plain, (((k1_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['93', '96', '97'])).
% 0.19/0.49  thf('99', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['92', '98'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
