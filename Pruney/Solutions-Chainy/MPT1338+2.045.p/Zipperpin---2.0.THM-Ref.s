%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mId11qhXgt

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:54 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 600 expanded)
%              Number of leaves         :   42 ( 191 expanded)
%              Depth                    :   19
%              Number of atoms          : 1639 (15969 expanded)
%              Number of equality atoms :  130 ( 892 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('3',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('17',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X24 @ X26 )
       != X24 )
      | ~ ( v2_funct_1 @ X26 )
      | ( ( k2_tops_2 @ X25 @ X24 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ X1 )
        = ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('51',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','26','33','42','43','51'])).

thf('53',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relset_1 @ X21 @ X20 @ X19 )
       != X20 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('60',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('65',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','15','16','53','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('68',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['52'])).

thf('69',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('81',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('85',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('92',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['66','92'])).

thf('94',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('95',plain,(
    ! [X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('97',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X17 )
      | ( zip_tseitin_1 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('98',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ( X13
        = ( k1_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( zip_tseitin_1 @ X15 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('102',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','106'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('108',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('109',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['94','114'])).

thf('116',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['93','117'])).

thf('119',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['39','40'])).

thf('121',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(simplify,[status(thm)],['121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mId11qhXgt
% 0.18/0.37  % Computer   : n025.cluster.edu
% 0.18/0.37  % Model      : x86_64 x86_64
% 0.18/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.37  % Memory     : 8042.1875MB
% 0.18/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.37  % CPULimit   : 60
% 0.18/0.37  % DateTime   : Tue Dec  1 16:50:36 EST 2020
% 0.18/0.37  % CPUTime    : 
% 0.18/0.37  % Running portfolio for 600 s
% 0.18/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.37  % Number of cores: 8
% 0.18/0.37  % Python version: Python 3.6.8
% 0.18/0.38  % Running in FO mode
% 0.73/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.93  % Solved by: fo/fo7.sh
% 0.73/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.93  % done 290 iterations in 0.483s
% 0.73/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.93  % SZS output start Refutation
% 0.73/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.73/0.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.73/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.73/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.73/0.93  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.73/0.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.73/0.93  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.73/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.73/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.73/0.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.73/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.93  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.73/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.73/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.73/0.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.73/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.73/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.73/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.73/0.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.73/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.73/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.73/0.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.73/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.93  thf(t37_relat_1, axiom,
% 0.73/0.93    (![A:$i]:
% 0.73/0.93     ( ( v1_relat_1 @ A ) =>
% 0.73/0.93       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.73/0.93         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.73/0.93  thf('0', plain,
% 0.73/0.93      (![X0 : $i]:
% 0.73/0.93         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 0.73/0.93          | ~ (v1_relat_1 @ X0))),
% 0.73/0.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.73/0.93  thf(d3_struct_0, axiom,
% 0.73/0.93    (![A:$i]:
% 0.73/0.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.73/0.93  thf('1', plain,
% 0.73/0.93      (![X22 : $i]:
% 0.73/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.73/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.73/0.93  thf('2', plain,
% 0.73/0.93      (![X22 : $i]:
% 0.73/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.73/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.73/0.93  thf(t62_tops_2, conjecture,
% 0.73/0.93    (![A:$i]:
% 0.73/0.93     ( ( l1_struct_0 @ A ) =>
% 0.73/0.93       ( ![B:$i]:
% 0.73/0.93         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.73/0.93           ( ![C:$i]:
% 0.73/0.93             ( ( ( v1_funct_1 @ C ) & 
% 0.73/0.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                 ( m1_subset_1 @
% 0.73/0.93                   C @ 
% 0.73/0.93                   ( k1_zfmisc_1 @
% 0.73/0.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93               ( ( ( ( k2_relset_1 @
% 0.73/0.93                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.73/0.93                     ( k2_struct_0 @ B ) ) & 
% 0.73/0.93                   ( v2_funct_1 @ C ) ) =>
% 0.73/0.93                 ( ( ( k1_relset_1 @
% 0.73/0.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.73/0.93                       ( k2_tops_2 @
% 0.73/0.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.73/0.93                     ( k2_struct_0 @ B ) ) & 
% 0.73/0.93                   ( ( k2_relset_1 @
% 0.73/0.93                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.73/0.93                       ( k2_tops_2 @
% 0.73/0.93                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.73/0.93                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.73/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.93    (~( ![A:$i]:
% 0.73/0.93        ( ( l1_struct_0 @ A ) =>
% 0.73/0.93          ( ![B:$i]:
% 0.73/0.93            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.73/0.93              ( ![C:$i]:
% 0.73/0.93                ( ( ( v1_funct_1 @ C ) & 
% 0.73/0.93                    ( v1_funct_2 @
% 0.73/0.93                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.73/0.93                    ( m1_subset_1 @
% 0.73/0.93                      C @ 
% 0.73/0.93                      ( k1_zfmisc_1 @
% 0.73/0.93                        ( k2_zfmisc_1 @
% 0.73/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.73/0.93                  ( ( ( ( k2_relset_1 @
% 0.73/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.73/0.93                        ( k2_struct_0 @ B ) ) & 
% 0.73/0.93                      ( v2_funct_1 @ C ) ) =>
% 0.73/0.93                    ( ( ( k1_relset_1 @
% 0.73/0.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.73/0.93                          ( k2_tops_2 @
% 0.73/0.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.73/0.93                        ( k2_struct_0 @ B ) ) & 
% 0.73/0.93                      ( ( k2_relset_1 @
% 0.73/0.93                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.73/0.93                          ( k2_tops_2 @
% 0.73/0.93                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.73/0.93                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.73/0.93    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.73/0.93  thf('3', plain,
% 0.73/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93          != (k2_struct_0 @ sk_B))
% 0.73/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93            != (k2_struct_0 @ sk_A)))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('4', plain,
% 0.73/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93          != (k2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93                = (k2_struct_0 @ sk_A))))),
% 0.73/0.93      inference('split', [status(esa)], ['3'])).
% 0.73/0.93  thf('5', plain,
% 0.73/0.93      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93           != (k2_struct_0 @ sk_A))
% 0.73/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.73/0.93         <= (~
% 0.73/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93                = (k2_struct_0 @ sk_A))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['2', '4'])).
% 0.73/0.93  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('7', plain,
% 0.73/0.93      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93          != (k2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93                = (k2_struct_0 @ sk_A))))),
% 0.73/0.93      inference('demod', [status(thm)], ['5', '6'])).
% 0.73/0.93  thf('8', plain,
% 0.73/0.93      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93           != (k2_struct_0 @ sk_A))
% 0.73/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.73/0.93         <= (~
% 0.73/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93                = (k2_struct_0 @ sk_A))))),
% 0.73/0.93      inference('sup-', [status(thm)], ['1', '7'])).
% 0.73/0.93  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf('10', plain,
% 0.73/0.93      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93          != (k2_struct_0 @ sk_A)))
% 0.73/0.93         <= (~
% 0.73/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.73/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.73/0.93                = (k2_struct_0 @ sk_A))))),
% 0.73/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.73/0.93  thf('11', plain,
% 0.73/0.93      ((m1_subset_1 @ sk_C @ 
% 0.73/0.93        (k1_zfmisc_1 @ 
% 0.73/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.73/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.93  thf(redefinition_k2_relset_1, axiom,
% 0.73/0.93    (![A:$i,B:$i,C:$i]:
% 0.73/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.93       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.77/0.93  thf('12', plain,
% 0.77/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.93         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.77/0.93          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.77/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.93  thf('13', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93         = (k2_relat_1 @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.93  thf('14', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93         = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('17', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf('18', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('19', plain,
% 0.77/0.93      (((m1_subset_1 @ sk_C @ 
% 0.77/0.93         (k1_zfmisc_1 @ 
% 0.77/0.93          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.77/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['17', '18'])).
% 0.77/0.93  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('21', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.93  thf('22', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('23', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.77/0.93      inference('demod', [status(thm)], ['21', '22'])).
% 0.77/0.93  thf(d4_tops_2, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.77/0.93         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.77/0.93  thf('24', plain,
% 0.77/0.93      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.77/0.93         (((k2_relset_1 @ X25 @ X24 @ X26) != (X24))
% 0.77/0.93          | ~ (v2_funct_1 @ X26)
% 0.77/0.93          | ((k2_tops_2 @ X25 @ X24 @ X26) = (k2_funct_1 @ X26))
% 0.77/0.93          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.77/0.93          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 0.77/0.93          | ~ (v1_funct_1 @ X26))),
% 0.77/0.93      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.77/0.93  thf('25', plain,
% 0.77/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.77/0.93        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93            = (k2_funct_1 @ sk_C))
% 0.77/0.93        | ~ (v2_funct_1 @ sk_C)
% 0.77/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93            != (k2_relat_1 @ sk_C)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.93  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('27', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf('28', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('29', plain,
% 0.77/0.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.77/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/0.93  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('31', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.93  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('33', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['31', '32'])).
% 0.77/0.93  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf(d9_funct_1, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.93       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.77/0.93  thf('35', plain,
% 0.77/0.93      (![X1 : $i]:
% 0.77/0.93         (~ (v2_funct_1 @ X1)
% 0.77/0.93          | ((k2_funct_1 @ X1) = (k4_relat_1 @ X1))
% 0.77/0.93          | ~ (v1_funct_1 @ X1)
% 0.77/0.93          | ~ (v1_relat_1 @ X1))),
% 0.77/0.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.77/0.93  thf('36', plain,
% 0.77/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.77/0.93        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.77/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.93  thf('37', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('38', plain,
% 0.77/0.93      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['36', '37'])).
% 0.77/0.93  thf('39', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf(cc1_relset_1, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.93       ( v1_relat_1 @ C ) ))).
% 0.77/0.93  thf('40', plain,
% 0.77/0.93      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.93         ((v1_relat_1 @ X2)
% 0.77/0.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.77/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.93  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.93  thf('42', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['38', '41'])).
% 0.77/0.93  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('44', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf('45', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93         = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('46', plain,
% 0.77/0.93      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93          = (k2_struct_0 @ sk_B))
% 0.77/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.93  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('48', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93         = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('demod', [status(thm)], ['46', '47'])).
% 0.77/0.93  thf('49', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('50', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('51', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93         = (k2_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.77/0.93  thf('52', plain,
% 0.77/0.93      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93          = (k4_relat_1 @ sk_C))
% 0.77/0.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['25', '26', '33', '42', '43', '51'])).
% 0.77/0.93  thf('53', plain,
% 0.77/0.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93         = (k4_relat_1 @ sk_C))),
% 0.77/0.93      inference('simplify', [status(thm)], ['52'])).
% 0.77/0.93  thf('54', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.77/0.93      inference('demod', [status(thm)], ['21', '22'])).
% 0.77/0.93  thf(t31_funct_2, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.93       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.93         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.93           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.93           ( m1_subset_1 @
% 0.77/0.93             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.77/0.93  thf('55', plain,
% 0.77/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.93         (~ (v2_funct_1 @ X19)
% 0.77/0.93          | ((k2_relset_1 @ X21 @ X20 @ X19) != (X20))
% 0.77/0.93          | (m1_subset_1 @ (k2_funct_1 @ X19) @ 
% 0.77/0.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.77/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.77/0.93          | ~ (v1_funct_2 @ X19 @ X21 @ X20)
% 0.77/0.93          | ~ (v1_funct_1 @ X19))),
% 0.77/0.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.77/0.93  thf('56', plain,
% 0.77/0.93      ((~ (v1_funct_1 @ sk_C)
% 0.77/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.77/0.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.77/0.93           (k1_zfmisc_1 @ 
% 0.77/0.93            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.77/0.93        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93            != (k2_relat_1 @ sk_C))
% 0.77/0.93        | ~ (v2_funct_1 @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['54', '55'])).
% 0.77/0.93  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('58', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['31', '32'])).
% 0.77/0.93  thf('59', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['38', '41'])).
% 0.77/0.93  thf('60', plain,
% 0.77/0.93      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93         = (k2_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.77/0.93  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('62', plain,
% 0.77/0.93      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.77/0.93         (k1_zfmisc_1 @ 
% 0.77/0.93          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.77/0.93        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['56', '57', '58', '59', '60', '61'])).
% 0.77/0.93  thf('63', plain,
% 0.77/0.93      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.77/0.93      inference('simplify', [status(thm)], ['62'])).
% 0.77/0.93  thf('64', plain,
% 0.77/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.77/0.93         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.77/0.93          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.77/0.93      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.93  thf('65', plain,
% 0.77/0.93      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['63', '64'])).
% 0.77/0.93  thf('66', plain,
% 0.77/0.93      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_A))))),
% 0.77/0.93      inference('demod', [status(thm)], ['10', '15', '16', '53', '65'])).
% 0.77/0.93  thf('67', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 0.77/0.93          | ~ (v1_relat_1 @ X0))),
% 0.77/0.93      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.77/0.93  thf('68', plain,
% 0.77/0.93      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.77/0.93         = (k4_relat_1 @ sk_C))),
% 0.77/0.93      inference('simplify', [status(thm)], ['52'])).
% 0.77/0.93  thf('69', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf('70', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf('71', plain,
% 0.77/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          != (k2_struct_0 @ sk_B)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('split', [status(esa)], ['3'])).
% 0.77/0.93  thf('72', plain,
% 0.77/0.93      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93           != (k2_struct_0 @ sk_B))
% 0.77/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['70', '71'])).
% 0.77/0.93  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('74', plain,
% 0.77/0.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          != (k2_struct_0 @ sk_B)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['72', '73'])).
% 0.77/0.93  thf('75', plain,
% 0.77/0.93      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93           != (k2_struct_0 @ sk_B))
% 0.77/0.93         | ~ (l1_struct_0 @ sk_B)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['69', '74'])).
% 0.77/0.93  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('77', plain,
% 0.77/0.93      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          != (k2_struct_0 @ sk_B)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['75', '76'])).
% 0.77/0.93  thf('78', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('79', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf('81', plain,
% 0.77/0.93      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.77/0.93          != (k2_relat_1 @ sk_C)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.77/0.93  thf('82', plain,
% 0.77/0.93      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['68', '81'])).
% 0.77/0.93  thf('83', plain,
% 0.77/0.93      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.77/0.93      inference('simplify', [status(thm)], ['62'])).
% 0.77/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.77/0.93  thf('84', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.93         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.77/0.93          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.77/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.93  thf('85', plain,
% 0.77/0.93      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['83', '84'])).
% 0.77/0.93  thf('86', plain,
% 0.77/0.93      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['82', '85'])).
% 0.77/0.93  thf('87', plain,
% 0.77/0.93      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['67', '86'])).
% 0.77/0.93  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.93  thf('89', plain,
% 0.77/0.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.77/0.93         <= (~
% 0.77/0.93             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93                = (k2_struct_0 @ sk_B))))),
% 0.77/0.93      inference('demod', [status(thm)], ['87', '88'])).
% 0.77/0.93  thf('90', plain,
% 0.77/0.93      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          = (k2_struct_0 @ sk_B)))),
% 0.77/0.93      inference('simplify', [status(thm)], ['89'])).
% 0.77/0.93  thf('91', plain,
% 0.77/0.93      (~
% 0.77/0.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          = (k2_struct_0 @ sk_A))) | 
% 0.77/0.93       ~
% 0.77/0.93       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          = (k2_struct_0 @ sk_B)))),
% 0.77/0.93      inference('split', [status(esa)], ['3'])).
% 0.77/0.93  thf('92', plain,
% 0.77/0.93      (~
% 0.77/0.93       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.77/0.93          = (k2_struct_0 @ sk_A)))),
% 0.77/0.93      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.77/0.93  thf('93', plain,
% 0.77/0.93      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.77/0.93      inference('simpl_trail', [status(thm)], ['66', '92'])).
% 0.77/0.93  thf('94', plain,
% 0.77/0.93      (![X22 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.77/0.93  thf(d1_funct_2, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.93  thf(zf_stmt_1, axiom,
% 0.77/0.93    (![B:$i,A:$i]:
% 0.77/0.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.93       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.93  thf('95', plain,
% 0.77/0.93      (![X11 : $i, X12 : $i]:
% 0.77/0.93         ((zip_tseitin_0 @ X11 @ X12) | ((X11) = (k1_xboole_0)))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.93  thf('96', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.93  thf(zf_stmt_3, axiom,
% 0.77/0.93    (![C:$i,B:$i,A:$i]:
% 0.77/0.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.93  thf(zf_stmt_5, axiom,
% 0.77/0.93    (![A:$i,B:$i,C:$i]:
% 0.77/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.93  thf('97', plain,
% 0.77/0.93      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.77/0.93         (~ (zip_tseitin_0 @ X16 @ X17)
% 0.77/0.93          | (zip_tseitin_1 @ X18 @ X16 @ X17)
% 0.77/0.93          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.93  thf('98', plain,
% 0.77/0.93      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.93        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/0.93  thf('99', plain,
% 0.77/0.93      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.77/0.93        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['95', '98'])).
% 0.77/0.93  thf('100', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('101', plain,
% 0.77/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.77/0.93         (~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.77/0.93          | ((X13) = (k1_relset_1 @ X13 @ X14 @ X15))
% 0.77/0.93          | ~ (zip_tseitin_1 @ X15 @ X14 @ X13))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.93  thf('102', plain,
% 0.77/0.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.93        | ((u1_struct_0 @ sk_A)
% 0.77/0.93            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['100', '101'])).
% 0.77/0.93  thf('103', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('104', plain,
% 0.77/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.93         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.77/0.93          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.77/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.93  thf('105', plain,
% 0.77/0.93      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.77/0.93         = (k1_relat_1 @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['103', '104'])).
% 0.77/0.93  thf('106', plain,
% 0.77/0.93      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.77/0.93      inference('demod', [status(thm)], ['102', '105'])).
% 0.77/0.93  thf('107', plain,
% 0.77/0.93      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.77/0.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['99', '106'])).
% 0.77/0.93  thf(fc2_struct_0, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.77/0.93       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/0.93  thf('108', plain,
% 0.77/0.93      (![X23 : $i]:
% 0.77/0.93         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.77/0.93          | ~ (l1_struct_0 @ X23)
% 0.77/0.93          | (v2_struct_0 @ X23))),
% 0.77/0.93      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.77/0.93  thf('109', plain,
% 0.77/0.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/0.93        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.77/0.93        | (v2_struct_0 @ sk_B)
% 0.77/0.93        | ~ (l1_struct_0 @ sk_B))),
% 0.77/0.93      inference('sup-', [status(thm)], ['107', '108'])).
% 0.77/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.93  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.93  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('112', plain,
% 0.77/0.93      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.77/0.93      inference('demod', [status(thm)], ['109', '110', '111'])).
% 0.77/0.93  thf('113', plain, (~ (v2_struct_0 @ sk_B)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('114', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.77/0.93      inference('clc', [status(thm)], ['112', '113'])).
% 0.77/0.93  thf('115', plain,
% 0.77/0.93      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 0.77/0.93      inference('sup+', [status(thm)], ['94', '114'])).
% 0.77/0.93  thf('116', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('117', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['115', '116'])).
% 0.77/0.93  thf('118', plain,
% 0.77/0.93      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['93', '117'])).
% 0.77/0.93  thf('119', plain,
% 0.77/0.93      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 0.77/0.93      inference('sup-', [status(thm)], ['0', '118'])).
% 0.77/0.93  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.77/0.93  thf('121', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.77/0.93      inference('demod', [status(thm)], ['119', '120'])).
% 0.77/0.93  thf('122', plain, ($false), inference('simplify', [status(thm)], ['121'])).
% 0.77/0.93  
% 0.77/0.93  % SZS output end Refutation
% 0.77/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
