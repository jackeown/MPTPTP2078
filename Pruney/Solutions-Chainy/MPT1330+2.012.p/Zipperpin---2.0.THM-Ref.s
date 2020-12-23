%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eRB0RPaSKG

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 374 expanded)
%              Number of leaves         :   44 ( 126 expanded)
%              Depth                    :   25
%              Number of atoms          : 1223 (5110 expanded)
%              Number of equality atoms :  116 ( 453 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( v1_partfun1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ( v1_partfun1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','21'])).

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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('33',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('35',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','39'])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('49',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( v5_relat_1 @ k1_xboole_0 @ X0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ k1_xboole_0 )
        | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('61',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('65',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ k1_xboole_0 @ X0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','63','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','62'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( k5_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
        = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ k1_xboole_0 )
          = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
        | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('81',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','62'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82','83'])).

thf('85',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','85'])).

thf('87',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('89',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','89'])).

thf('91',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','90'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('92',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('95',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('98',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('99',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','96','99'])).

thf('101',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    v5_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('115',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ X13 ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B_1 ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('119',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B_1 ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('121',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['94','95'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['101','104','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eRB0RPaSKG
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 229 iterations in 0.095s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.19/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.55  thf(d3_struct_0, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf(t52_tops_2, conjecture,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_struct_0 @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( l1_struct_0 @ B ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                 ( m1_subset_1 @
% 0.19/0.55                   C @ 
% 0.19/0.55                   ( k1_zfmisc_1 @
% 0.19/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.55                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.55                 ( ( k8_relset_1 @
% 0.19/0.55                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.55                     ( k2_struct_0 @ B ) ) =
% 0.19/0.55                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i]:
% 0.19/0.55        ( ( l1_struct_0 @ A ) =>
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ( l1_struct_0 @ B ) =>
% 0.19/0.55              ( ![C:$i]:
% 0.19/0.55                ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55                    ( v1_funct_2 @
% 0.19/0.55                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.55                    ( m1_subset_1 @
% 0.19/0.55                      C @ 
% 0.19/0.55                      ( k1_zfmisc_1 @
% 0.19/0.55                        ( k2_zfmisc_1 @
% 0.19/0.55                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.55                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.19/0.55                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.55                    ( ( k8_relset_1 @
% 0.19/0.55                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.55                        ( k2_struct_0 @ B ) ) =
% 0.19/0.55                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ 
% 0.19/0.55         (k1_zfmisc_1 @ 
% 0.19/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ 
% 0.19/0.55         (k1_zfmisc_1 @ 
% 0.19/0.55          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['0', '5'])).
% 0.19/0.55  thf('7', plain, ((l1_struct_0 @ sk_B_1)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.55  thf(t132_funct_2, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.55       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.55           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.55           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.55         (((X34) = (k1_xboole_0))
% 0.19/0.55          | ~ (v1_funct_1 @ X35)
% 0.19/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.19/0.55          | (v1_partfun1 @ X35 @ X36)
% 0.19/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.19/0.55          | ~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.19/0.55          | ~ (v1_funct_1 @ X35))),
% 0.19/0.55      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.19/0.55         (~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.19/0.55          | (v1_partfun1 @ X35 @ X36)
% 0.19/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.19/0.55          | ~ (v1_funct_1 @ X35)
% 0.19/0.55          | ((X34) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.19/0.55        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '10'])).
% 0.19/0.55  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.55  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['13', '18'])).
% 0.19/0.55  thf('20', plain, ((l1_struct_0 @ sk_B_1)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.19/0.55        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['11', '12', '21'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.19/0.55        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 0.19/0.55         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['23'])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['23'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.55  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['25', '30'])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['23'])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.55  thf(t6_mcart_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.55                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.19/0.55                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.19/0.55                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.19/0.55                       ( r2_hidden @ G @ B ) ) =>
% 0.19/0.55                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (![X26 : $i]:
% 0.19/0.55         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.19/0.55      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('split', [status(esa)], ['23'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ 
% 0.19/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.55  thf(t113_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X1 : $i, X2 : $i]:
% 0.19/0.55         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '39'])).
% 0.19/0.55  thf(t5_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.19/0.55          | ~ (v1_xboole_0 @ X5)
% 0.19/0.55          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.55  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['34', '44'])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ k1_xboole_0 @ 
% 0.19/0.55          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['33', '45'])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['37', '39'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      ((((sk_C) = (k1_xboole_0))) <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['34', '44'])).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.19/0.55  thf('51', plain,
% 0.19/0.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.19/0.55          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.55          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.19/0.55              = (k10_relat_1 @ X1 @ X2)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      ((![X0 : $i, X1 : $i]:
% 0.19/0.55          ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0)
% 0.19/0.55            = (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['49', '52'])).
% 0.19/0.55  thf('54', plain,
% 0.19/0.55      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.19/0.55      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.55  thf(cc2_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.55  thf('56', plain,
% 0.19/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.55         ((v5_relat_1 @ X19 @ X21)
% 0.19/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.19/0.55          | (v5_relat_1 @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      ((![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['54', '57'])).
% 0.19/0.55  thf(d19_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ B ) =>
% 0.19/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i]:
% 0.19/0.55         (~ (v5_relat_1 @ X6 @ X7)
% 0.19/0.55          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.19/0.55          | ~ (v1_relat_1 @ X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.55           | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.55  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.55  thf('61', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.55  thf(fc3_funct_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.55  thf('62', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.55  thf('64', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.55  thf(t71_relat_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.55  thf('65', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.55  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.19/0.55  thf('67', plain,
% 0.19/0.55      ((![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['60', '63', '66'])).
% 0.19/0.55  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.19/0.55  thf(t79_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ B ) =>
% 0.19/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.55         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.19/0.55  thf('69', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i]:
% 0.19/0.55         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.19/0.55          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 0.19/0.55          | ~ (v1_relat_1 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.55  thf('70', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.19/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.55          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.19/0.55  thf('71', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.55  thf('72', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.19/0.55          | ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.19/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.55  thf('73', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          ((k5_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ X0)) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['67', '72'])).
% 0.19/0.55  thf('74', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.19/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.55  thf(t182_relat_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( v1_relat_1 @ B ) =>
% 0.19/0.55           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.19/0.55             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.55  thf('75', plain,
% 0.19/0.55      (![X8 : $i, X9 : $i]:
% 0.19/0.55         (~ (v1_relat_1 @ X8)
% 0.19/0.55          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.19/0.55              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.19/0.55          | ~ (v1_relat_1 @ X9))),
% 0.19/0.55      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.19/0.55  thf('76', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ X1)
% 0.19/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['74', '75'])).
% 0.19/0.55  thf('77', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.55  thf('78', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ X1))),
% 0.19/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.55  thf('79', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          (((k1_relat_1 @ k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.55           | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['73', '78'])).
% 0.19/0.55  thf('80', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.19/0.55  thf('81', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.19/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.55  thf('82', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.55      inference('sup+', [status(thm)], ['80', '81'])).
% 0.19/0.55  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.19/0.55  thf('84', plain,
% 0.19/0.55      ((![X0 : $i]: ((k1_xboole_0) = (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['79', '82', '83'])).
% 0.19/0.55  thf('85', plain,
% 0.19/0.55      ((![X0 : $i, X1 : $i]:
% 0.19/0.55          ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['53', '84'])).
% 0.19/0.55  thf('86', plain,
% 0.19/0.55      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.55         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.55      inference('demod', [status(thm)], ['46', '85'])).
% 0.19/0.55  thf('87', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['86'])).
% 0.19/0.55  thf('88', plain,
% 0.19/0.55      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 0.19/0.55       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.55      inference('split', [status(esa)], ['23'])).
% 0.19/0.55  thf('89', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.19/0.55  thf('90', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['24', '89'])).
% 0.19/0.55  thf('91', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['22', '90'])).
% 0.19/0.55  thf(d4_partfun1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.55       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.55  thf('92', plain,
% 0.19/0.55      (![X32 : $i, X33 : $i]:
% 0.19/0.55         (~ (v1_partfun1 @ X33 @ X32)
% 0.19/0.55          | ((k1_relat_1 @ X33) = (X32))
% 0.19/0.55          | ~ (v4_relat_1 @ X33 @ X32)
% 0.19/0.55          | ~ (v1_relat_1 @ X33))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.55  thf('93', plain,
% 0.19/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.19/0.55        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.19/0.55  thf('94', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(cc1_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( v1_relat_1 @ C ) ))).
% 0.19/0.55  thf('95', plain,
% 0.19/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.55         ((v1_relat_1 @ X16)
% 0.19/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.55  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.55  thf('97', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.55  thf('98', plain,
% 0.19/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.55         ((v4_relat_1 @ X19 @ X20)
% 0.19/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.55  thf('99', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.19/0.55  thf('100', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['93', '96', '99'])).
% 0.19/0.55  thf('101', plain,
% 0.19/0.55      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.19/0.55         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('102', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('103', plain,
% 0.19/0.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.19/0.55          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.19/0.55  thf('104', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.55           sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['102', '103'])).
% 0.19/0.55  thf('105', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.19/0.55  thf('106', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('107', plain,
% 0.19/0.55      (((m1_subset_1 @ sk_C @ 
% 0.19/0.55         (k1_zfmisc_1 @ 
% 0.19/0.55          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 0.19/0.55        | ~ (l1_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['105', '106'])).
% 0.19/0.55  thf('108', plain, ((l1_struct_0 @ sk_B_1)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('109', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ 
% 0.19/0.55        (k1_zfmisc_1 @ 
% 0.19/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.19/0.55      inference('demod', [status(thm)], ['107', '108'])).
% 0.19/0.55  thf('110', plain,
% 0.19/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.55         ((v5_relat_1 @ X19 @ X21)
% 0.19/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.55  thf('111', plain, ((v5_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['109', '110'])).
% 0.19/0.55  thf('112', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i]:
% 0.19/0.55         (~ (v5_relat_1 @ X6 @ X7)
% 0.19/0.55          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.19/0.55          | ~ (v1_relat_1 @ X6))),
% 0.19/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.55  thf('113', plain,
% 0.19/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['111', '112'])).
% 0.19/0.55  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.55  thf('115', plain,
% 0.19/0.55      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['113', '114'])).
% 0.19/0.55  thf('116', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i]:
% 0.19/0.55         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.19/0.55          | ((k5_relat_1 @ X12 @ (k6_relat_1 @ X13)) = (X12))
% 0.19/0.55          | ~ (v1_relat_1 @ X12))),
% 0.19/0.55      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.19/0.55  thf('117', plain,
% 0.19/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.55        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_struct_0 @ sk_B_1))) = (sk_C)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['115', '116'])).
% 0.19/0.55  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.55  thf('119', plain,
% 0.19/0.55      (((k5_relat_1 @ sk_C @ (k6_relat_1 @ (k2_struct_0 @ sk_B_1))) = (sk_C))),
% 0.19/0.55      inference('demod', [status(thm)], ['117', '118'])).
% 0.19/0.55  thf('120', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.19/0.55            = (k10_relat_1 @ X1 @ X0))
% 0.19/0.55          | ~ (v1_relat_1 @ X1))),
% 0.19/0.55      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.55  thf('121', plain,
% 0.19/0.55      ((((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))
% 0.19/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.55      inference('sup+', [status(thm)], ['119', '120'])).
% 0.19/0.55  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.55      inference('sup-', [status(thm)], ['94', '95'])).
% 0.19/0.55  thf('123', plain,
% 0.19/0.55      (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k2_struct_0 @ sk_B_1)))),
% 0.19/0.55      inference('demod', [status(thm)], ['121', '122'])).
% 0.19/0.55  thf('124', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['101', '104', '123'])).
% 0.19/0.55  thf('125', plain, ($false),
% 0.19/0.55      inference('simplify_reflect-', [status(thm)], ['100', '124'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
