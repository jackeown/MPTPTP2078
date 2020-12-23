%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:03 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.27s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 261 expanded)
%              Number of leaves         :   37 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  295 (1233 expanded)
%              Number of equality atoms :  102 ( 394 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(c_44,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_116,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_116])).

tff(c_136,plain,(
    ! [B_60,A_61,C_62] :
      ( k1_xboole_0 = B_60
      | k1_relset_1(A_61,B_60,C_62) = A_61
      | ~ v1_funct_2(C_62,A_61,B_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_136])).

tff(c_145,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_123,c_139])).

tff(c_146,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_145])).

tff(c_81,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_89,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_81])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_50,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_97,plain,(
    ! [A_47,B_48,C_49] :
      ( k2_relset_1(A_47,B_48,C_49) = k2_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_103,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_97])).

tff(c_106,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_103])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_124,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_116])).

tff(c_142,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_136])).

tff(c_149,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_124,c_142])).

tff(c_150,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_149])).

tff(c_32,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k2_funct_1(A_1) = B_3
      | k6_relat_1(k1_relat_1(A_1)) != k5_relat_1(A_1,B_3)
      | k2_relat_1(A_1) != k1_relat_1(B_3)
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9076,plain,(
    ! [A_401,B_402] :
      ( k2_funct_1(A_401) = B_402
      | k6_partfun1(k1_relat_1(A_401)) != k5_relat_1(A_401,B_402)
      | k2_relat_1(A_401) != k1_relat_1(B_402)
      | ~ v2_funct_1(A_401)
      | ~ v1_funct_1(B_402)
      | ~ v1_relat_1(B_402)
      | ~ v1_funct_1(A_401)
      | ~ v1_relat_1(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2])).

tff(c_9078,plain,(
    ! [B_402] :
      ( k2_funct_1('#skF_3') = B_402
      | k5_relat_1('#skF_3',B_402) != k6_partfun1('#skF_1')
      | k2_relat_1('#skF_3') != k1_relat_1(B_402)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_402)
      | ~ v1_relat_1(B_402)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_9076])).

tff(c_9102,plain,(
    ! [B_403] :
      ( k2_funct_1('#skF_3') = B_403
      | k5_relat_1('#skF_3',B_403) != k6_partfun1('#skF_1')
      | k1_relat_1(B_403) != '#skF_2'
      | ~ v1_funct_1(B_403)
      | ~ v1_relat_1(B_403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_66,c_50,c_106,c_9078])).

tff(c_9111,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_9102])).

tff(c_9118,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_146,c_9111])).

tff(c_9119,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9118])).

tff(c_34,plain,(
    ! [C_35,B_34,A_33] :
      ( m1_subset_1(k2_funct_1(C_35),k1_zfmisc_1(k2_zfmisc_1(B_34,A_33)))
      | k2_relset_1(A_33,B_34,C_35) != B_34
      | ~ v2_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34)))
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_388,plain,(
    ! [A_102,C_104,D_100,E_105,B_101,F_103] :
      ( k1_partfun1(A_102,B_101,C_104,D_100,E_105,F_103) = k5_relat_1(E_105,F_103)
      | ~ m1_subset_1(F_103,k1_zfmisc_1(k2_zfmisc_1(C_104,D_100)))
      | ~ v1_funct_1(F_103)
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_1(E_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_392,plain,(
    ! [A_102,B_101,E_105] :
      ( k1_partfun1(A_102,B_101,'#skF_2','#skF_1',E_105,'#skF_4') = k5_relat_1(E_105,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_105,k1_zfmisc_1(k2_zfmisc_1(A_102,B_101)))
      | ~ v1_funct_1(E_105) ) ),
    inference(resolution,[status(thm)],[c_56,c_388])).

tff(c_402,plain,(
    ! [A_106,B_107,E_108] :
      ( k1_partfun1(A_106,B_107,'#skF_2','#skF_1',E_108,'#skF_4') = k5_relat_1(E_108,'#skF_4')
      | ~ m1_subset_1(E_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107)))
      | ~ v1_funct_1(E_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_392])).

tff(c_411,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_402])).

tff(c_418,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_411])).

tff(c_52,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_184,plain,(
    ! [D_66,C_67,A_68,B_69] :
      ( D_66 = C_67
      | ~ r2_relset_1(A_68,B_69,C_67,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_191,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_52,c_184])).

tff(c_214,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_445,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_214])).

tff(c_568,plain,(
    ! [A_134,F_135,E_133,C_130,B_131,D_132] :
      ( m1_subset_1(k1_partfun1(A_134,B_131,C_130,D_132,E_133,F_135),k1_zfmisc_1(k2_zfmisc_1(A_134,D_132)))
      | ~ m1_subset_1(F_135,k1_zfmisc_1(k2_zfmisc_1(C_130,D_132)))
      | ~ v1_funct_1(F_135)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_131)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_647,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_568])).

tff(c_680,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_60,c_56,c_647])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_680])).

tff(c_683,plain,
    ( ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_717,plain,(
    ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_200,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_funct_1(k2_funct_1(C_70))
      | k2_relset_1(A_71,B_72,C_70) != B_72
      | ~ v2_funct_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72)))
      | ~ v1_funct_2(C_70,A_71,B_72)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_206,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_200])).

tff(c_212,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_206])).

tff(c_1097,plain,(
    ! [A_172,C_173,B_174] :
      ( k6_partfun1(A_172) = k5_relat_1(C_173,k2_funct_1(C_173))
      | k1_xboole_0 = B_174
      | ~ v2_funct_1(C_173)
      | k2_relset_1(A_172,B_174,C_173) != B_174
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_172,B_174)))
      | ~ v1_funct_2(C_173,A_172,B_174)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1105,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1097])).

tff(c_1117,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_54,c_50,c_1105])).

tff(c_1118,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1117])).

tff(c_849,plain,(
    ! [C_160,B_161,A_162] :
      ( m1_subset_1(k2_funct_1(C_160),k1_zfmisc_1(k2_zfmisc_1(B_161,A_162)))
      | k2_relset_1(A_162,B_161,C_160) != B_161
      | ~ v2_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161)))
      | ~ v1_funct_2(C_160,A_162,B_161)
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    ! [B_27,D_29,A_26,E_30,F_31,C_28] :
      ( k1_partfun1(A_26,B_27,C_28,D_29,E_30,F_31) = k5_relat_1(E_30,F_31)
      | ~ m1_subset_1(F_31,k1_zfmisc_1(k2_zfmisc_1(C_28,D_29)))
      | ~ v1_funct_1(F_31)
      | ~ m1_subset_1(E_30,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_1(E_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3995,plain,(
    ! [A_269,A_267,C_271,B_266,E_270,B_268] :
      ( k1_partfun1(A_267,B_266,B_268,A_269,E_270,k2_funct_1(C_271)) = k5_relat_1(E_270,k2_funct_1(C_271))
      | ~ v1_funct_1(k2_funct_1(C_271))
      | ~ m1_subset_1(E_270,k1_zfmisc_1(k2_zfmisc_1(A_267,B_266)))
      | ~ v1_funct_1(E_270)
      | k2_relset_1(A_269,B_268,C_271) != B_268
      | ~ v2_funct_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268)))
      | ~ v1_funct_2(C_271,A_269,B_268)
      | ~ v1_funct_1(C_271) ) ),
    inference(resolution,[status(thm)],[c_849,c_30])).

tff(c_4027,plain,(
    ! [B_268,A_269,C_271] :
      ( k1_partfun1('#skF_1','#skF_2',B_268,A_269,'#skF_3',k2_funct_1(C_271)) = k5_relat_1('#skF_3',k2_funct_1(C_271))
      | ~ v1_funct_1(k2_funct_1(C_271))
      | ~ v1_funct_1('#skF_3')
      | k2_relset_1(A_269,B_268,C_271) != B_268
      | ~ v2_funct_1(C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_269,B_268)))
      | ~ v1_funct_2(C_271,A_269,B_268)
      | ~ v1_funct_1(C_271) ) ),
    inference(resolution,[status(thm)],[c_62,c_3995])).

tff(c_8841,plain,(
    ! [B_398,A_399,C_400] :
      ( k1_partfun1('#skF_1','#skF_2',B_398,A_399,'#skF_3',k2_funct_1(C_400)) = k5_relat_1('#skF_3',k2_funct_1(C_400))
      | ~ v1_funct_1(k2_funct_1(C_400))
      | k2_relset_1(A_399,B_398,C_400) != B_398
      | ~ v2_funct_1(C_400)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_399,B_398)))
      | ~ v1_funct_2(C_400,A_399,B_398)
      | ~ v1_funct_1(C_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4027])).

tff(c_8901,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_8841])).

tff(c_8957,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_50,c_54,c_212,c_1118,c_8901])).

tff(c_26,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1(k1_partfun1(A_20,B_21,C_22,D_23,E_24,F_25),k1_zfmisc_1(k2_zfmisc_1(A_20,D_23)))
      | ~ m1_subset_1(F_25,k1_zfmisc_1(k2_zfmisc_1(C_22,D_23)))
      | ~ v1_funct_1(F_25)
      | ~ m1_subset_1(E_24,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_funct_1(E_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8989,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8957,c_26])).

tff(c_9018,plain,
    ( m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_212,c_8989])).

tff(c_9019,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_717,c_9018])).

tff(c_9023,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_9019])).

tff(c_9027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_50,c_54,c_9023])).

tff(c_9028,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_9219,plain,(
    ! [A_424,F_425,E_427,C_426,B_423,D_422] :
      ( k1_partfun1(A_424,B_423,C_426,D_422,E_427,F_425) = k5_relat_1(E_427,F_425)
      | ~ m1_subset_1(F_425,k1_zfmisc_1(k2_zfmisc_1(C_426,D_422)))
      | ~ v1_funct_1(F_425)
      | ~ m1_subset_1(E_427,k1_zfmisc_1(k2_zfmisc_1(A_424,B_423)))
      | ~ v1_funct_1(E_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_9223,plain,(
    ! [A_424,B_423,E_427] :
      ( k1_partfun1(A_424,B_423,'#skF_2','#skF_1',E_427,'#skF_4') = k5_relat_1(E_427,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_427,k1_zfmisc_1(k2_zfmisc_1(A_424,B_423)))
      | ~ v1_funct_1(E_427) ) ),
    inference(resolution,[status(thm)],[c_56,c_9219])).

tff(c_9235,plain,(
    ! [A_428,B_429,E_430] :
      ( k1_partfun1(A_428,B_429,'#skF_2','#skF_1',E_430,'#skF_4') = k5_relat_1(E_430,'#skF_4')
      | ~ m1_subset_1(E_430,k1_zfmisc_1(k2_zfmisc_1(A_428,B_429)))
      | ~ v1_funct_1(E_430) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_9223])).

tff(c_9244,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_9235])).

tff(c_9253,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_9028,c_9244])).

tff(c_9255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9119,c_9253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.17/3.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.17/3.99  
% 10.17/3.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/4.00  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.27/4.00  
% 10.27/4.00  %Foreground sorts:
% 10.27/4.00  
% 10.27/4.00  
% 10.27/4.00  %Background operators:
% 10.27/4.00  
% 10.27/4.00  
% 10.27/4.00  %Foreground operators:
% 10.27/4.00  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.27/4.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.27/4.00  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.27/4.00  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.27/4.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.27/4.00  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.27/4.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.27/4.00  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.27/4.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.27/4.00  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.27/4.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.27/4.00  tff('#skF_2', type, '#skF_2': $i).
% 10.27/4.00  tff('#skF_3', type, '#skF_3': $i).
% 10.27/4.00  tff('#skF_1', type, '#skF_1': $i).
% 10.27/4.00  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.27/4.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.27/4.00  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.27/4.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.27/4.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.27/4.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.27/4.00  tff('#skF_4', type, '#skF_4': $i).
% 10.27/4.00  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.27/4.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.27/4.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.27/4.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.27/4.00  
% 10.27/4.02  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.27/4.02  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 10.27/4.02  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 10.27/4.02  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.27/4.02  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.27/4.02  tff(f_104, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.27/4.02  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_funct_1)).
% 10.27/4.02  tff(f_120, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.27/4.02  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.27/4.02  tff(f_62, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.27/4.02  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.27/4.02  tff(f_136, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 10.27/4.02  tff(c_44, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_48, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_116, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.27/4.02  tff(c_123, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_116])).
% 10.27/4.02  tff(c_136, plain, (![B_60, A_61, C_62]: (k1_xboole_0=B_60 | k1_relset_1(A_61, B_60, C_62)=A_61 | ~v1_funct_2(C_62, A_61, B_60) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.27/4.02  tff(c_139, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_136])).
% 10.27/4.02  tff(c_145, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_123, c_139])).
% 10.27/4.02  tff(c_146, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_145])).
% 10.27/4.02  tff(c_81, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.27/4.02  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_81])).
% 10.27/4.02  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_89, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_81])).
% 10.27/4.02  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_50, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_97, plain, (![A_47, B_48, C_49]: (k2_relset_1(A_47, B_48, C_49)=k2_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.27/4.02  tff(c_103, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_97])).
% 10.27/4.02  tff(c_106, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_103])).
% 10.27/4.02  tff(c_46, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_124, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_116])).
% 10.27/4.02  tff(c_142, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_136])).
% 10.27/4.02  tff(c_149, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_124, c_142])).
% 10.27/4.02  tff(c_150, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_46, c_149])).
% 10.27/4.02  tff(c_32, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_104])).
% 10.27/4.02  tff(c_2, plain, (![A_1, B_3]: (k2_funct_1(A_1)=B_3 | k6_relat_1(k1_relat_1(A_1))!=k5_relat_1(A_1, B_3) | k2_relat_1(A_1)!=k1_relat_1(B_3) | ~v2_funct_1(A_1) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.27/4.02  tff(c_9076, plain, (![A_401, B_402]: (k2_funct_1(A_401)=B_402 | k6_partfun1(k1_relat_1(A_401))!=k5_relat_1(A_401, B_402) | k2_relat_1(A_401)!=k1_relat_1(B_402) | ~v2_funct_1(A_401) | ~v1_funct_1(B_402) | ~v1_relat_1(B_402) | ~v1_funct_1(A_401) | ~v1_relat_1(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2])).
% 10.27/4.02  tff(c_9078, plain, (![B_402]: (k2_funct_1('#skF_3')=B_402 | k5_relat_1('#skF_3', B_402)!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1(B_402) | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_402) | ~v1_relat_1(B_402) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_9076])).
% 10.27/4.02  tff(c_9102, plain, (![B_403]: (k2_funct_1('#skF_3')=B_403 | k5_relat_1('#skF_3', B_403)!=k6_partfun1('#skF_1') | k1_relat_1(B_403)!='#skF_2' | ~v1_funct_1(B_403) | ~v1_relat_1(B_403))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_66, c_50, c_106, c_9078])).
% 10.27/4.02  tff(c_9111, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_88, c_9102])).
% 10.27/4.02  tff(c_9118, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_146, c_9111])).
% 10.27/4.02  tff(c_9119, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_9118])).
% 10.27/4.02  tff(c_34, plain, (![C_35, B_34, A_33]: (m1_subset_1(k2_funct_1(C_35), k1_zfmisc_1(k2_zfmisc_1(B_34, A_33))) | k2_relset_1(A_33, B_34, C_35)!=B_34 | ~v2_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))) | ~v1_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.27/4.02  tff(c_388, plain, (![A_102, C_104, D_100, E_105, B_101, F_103]: (k1_partfun1(A_102, B_101, C_104, D_100, E_105, F_103)=k5_relat_1(E_105, F_103) | ~m1_subset_1(F_103, k1_zfmisc_1(k2_zfmisc_1(C_104, D_100))) | ~v1_funct_1(F_103) | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_1(E_105))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.27/4.02  tff(c_392, plain, (![A_102, B_101, E_105]: (k1_partfun1(A_102, B_101, '#skF_2', '#skF_1', E_105, '#skF_4')=k5_relat_1(E_105, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_105, k1_zfmisc_1(k2_zfmisc_1(A_102, B_101))) | ~v1_funct_1(E_105))), inference(resolution, [status(thm)], [c_56, c_388])).
% 10.27/4.02  tff(c_402, plain, (![A_106, B_107, E_108]: (k1_partfun1(A_106, B_107, '#skF_2', '#skF_1', E_108, '#skF_4')=k5_relat_1(E_108, '#skF_4') | ~m1_subset_1(E_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))) | ~v1_funct_1(E_108))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_392])).
% 10.27/4.02  tff(c_411, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_402])).
% 10.27/4.02  tff(c_418, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_411])).
% 10.27/4.02  tff(c_52, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.27/4.02  tff(c_184, plain, (![D_66, C_67, A_68, B_69]: (D_66=C_67 | ~r2_relset_1(A_68, B_69, C_67, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.27/4.02  tff(c_191, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_52, c_184])).
% 10.27/4.02  tff(c_214, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_191])).
% 10.27/4.02  tff(c_445, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_214])).
% 10.27/4.02  tff(c_568, plain, (![A_134, F_135, E_133, C_130, B_131, D_132]: (m1_subset_1(k1_partfun1(A_134, B_131, C_130, D_132, E_133, F_135), k1_zfmisc_1(k2_zfmisc_1(A_134, D_132))) | ~m1_subset_1(F_135, k1_zfmisc_1(k2_zfmisc_1(C_130, D_132))) | ~v1_funct_1(F_135) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_131))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.27/4.02  tff(c_647, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_418, c_568])).
% 10.27/4.02  tff(c_680, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_60, c_56, c_647])).
% 10.27/4.02  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_445, c_680])).
% 10.27/4.02  tff(c_683, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_191])).
% 10.27/4.02  tff(c_717, plain, (~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_683])).
% 10.27/4.02  tff(c_200, plain, (![C_70, A_71, B_72]: (v1_funct_1(k2_funct_1(C_70)) | k2_relset_1(A_71, B_72, C_70)!=B_72 | ~v2_funct_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))) | ~v1_funct_2(C_70, A_71, B_72) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.27/4.02  tff(c_206, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_200])).
% 10.27/4.02  tff(c_212, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_206])).
% 10.27/4.02  tff(c_1097, plain, (![A_172, C_173, B_174]: (k6_partfun1(A_172)=k5_relat_1(C_173, k2_funct_1(C_173)) | k1_xboole_0=B_174 | ~v2_funct_1(C_173) | k2_relset_1(A_172, B_174, C_173)!=B_174 | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_172, B_174))) | ~v1_funct_2(C_173, A_172, B_174) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.27/4.02  tff(c_1105, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1097])).
% 10.27/4.02  tff(c_1117, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_54, c_50, c_1105])).
% 10.27/4.02  tff(c_1118, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_46, c_1117])).
% 10.27/4.02  tff(c_849, plain, (![C_160, B_161, A_162]: (m1_subset_1(k2_funct_1(C_160), k1_zfmisc_1(k2_zfmisc_1(B_161, A_162))) | k2_relset_1(A_162, B_161, C_160)!=B_161 | ~v2_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))) | ~v1_funct_2(C_160, A_162, B_161) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.27/4.02  tff(c_30, plain, (![B_27, D_29, A_26, E_30, F_31, C_28]: (k1_partfun1(A_26, B_27, C_28, D_29, E_30, F_31)=k5_relat_1(E_30, F_31) | ~m1_subset_1(F_31, k1_zfmisc_1(k2_zfmisc_1(C_28, D_29))) | ~v1_funct_1(F_31) | ~m1_subset_1(E_30, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_1(E_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.27/4.02  tff(c_3995, plain, (![A_269, A_267, C_271, B_266, E_270, B_268]: (k1_partfun1(A_267, B_266, B_268, A_269, E_270, k2_funct_1(C_271))=k5_relat_1(E_270, k2_funct_1(C_271)) | ~v1_funct_1(k2_funct_1(C_271)) | ~m1_subset_1(E_270, k1_zfmisc_1(k2_zfmisc_1(A_267, B_266))) | ~v1_funct_1(E_270) | k2_relset_1(A_269, B_268, C_271)!=B_268 | ~v2_funct_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))) | ~v1_funct_2(C_271, A_269, B_268) | ~v1_funct_1(C_271))), inference(resolution, [status(thm)], [c_849, c_30])).
% 10.27/4.02  tff(c_4027, plain, (![B_268, A_269, C_271]: (k1_partfun1('#skF_1', '#skF_2', B_268, A_269, '#skF_3', k2_funct_1(C_271))=k5_relat_1('#skF_3', k2_funct_1(C_271)) | ~v1_funct_1(k2_funct_1(C_271)) | ~v1_funct_1('#skF_3') | k2_relset_1(A_269, B_268, C_271)!=B_268 | ~v2_funct_1(C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_269, B_268))) | ~v1_funct_2(C_271, A_269, B_268) | ~v1_funct_1(C_271))), inference(resolution, [status(thm)], [c_62, c_3995])).
% 10.27/4.02  tff(c_8841, plain, (![B_398, A_399, C_400]: (k1_partfun1('#skF_1', '#skF_2', B_398, A_399, '#skF_3', k2_funct_1(C_400))=k5_relat_1('#skF_3', k2_funct_1(C_400)) | ~v1_funct_1(k2_funct_1(C_400)) | k2_relset_1(A_399, B_398, C_400)!=B_398 | ~v2_funct_1(C_400) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_399, B_398))) | ~v1_funct_2(C_400, A_399, B_398) | ~v1_funct_1(C_400))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4027])).
% 10.27/4.02  tff(c_8901, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_8841])).
% 10.27/4.02  tff(c_8957, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_50, c_54, c_212, c_1118, c_8901])).
% 10.27/4.02  tff(c_26, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1(k1_partfun1(A_20, B_21, C_22, D_23, E_24, F_25), k1_zfmisc_1(k2_zfmisc_1(A_20, D_23))) | ~m1_subset_1(F_25, k1_zfmisc_1(k2_zfmisc_1(C_22, D_23))) | ~v1_funct_1(F_25) | ~m1_subset_1(E_24, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_funct_1(E_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.27/4.02  tff(c_8989, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8957, c_26])).
% 10.27/4.02  tff(c_9018, plain, (m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_212, c_8989])).
% 10.27/4.02  tff(c_9019, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_717, c_9018])).
% 10.27/4.02  tff(c_9023, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_9019])).
% 10.27/4.02  tff(c_9027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_50, c_54, c_9023])).
% 10.27/4.02  tff(c_9028, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_683])).
% 10.27/4.02  tff(c_9219, plain, (![A_424, F_425, E_427, C_426, B_423, D_422]: (k1_partfun1(A_424, B_423, C_426, D_422, E_427, F_425)=k5_relat_1(E_427, F_425) | ~m1_subset_1(F_425, k1_zfmisc_1(k2_zfmisc_1(C_426, D_422))) | ~v1_funct_1(F_425) | ~m1_subset_1(E_427, k1_zfmisc_1(k2_zfmisc_1(A_424, B_423))) | ~v1_funct_1(E_427))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.27/4.02  tff(c_9223, plain, (![A_424, B_423, E_427]: (k1_partfun1(A_424, B_423, '#skF_2', '#skF_1', E_427, '#skF_4')=k5_relat_1(E_427, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_427, k1_zfmisc_1(k2_zfmisc_1(A_424, B_423))) | ~v1_funct_1(E_427))), inference(resolution, [status(thm)], [c_56, c_9219])).
% 10.27/4.02  tff(c_9235, plain, (![A_428, B_429, E_430]: (k1_partfun1(A_428, B_429, '#skF_2', '#skF_1', E_430, '#skF_4')=k5_relat_1(E_430, '#skF_4') | ~m1_subset_1(E_430, k1_zfmisc_1(k2_zfmisc_1(A_428, B_429))) | ~v1_funct_1(E_430))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_9223])).
% 10.27/4.02  tff(c_9244, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_9235])).
% 10.27/4.02  tff(c_9253, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_9028, c_9244])).
% 10.27/4.02  tff(c_9255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9119, c_9253])).
% 10.27/4.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.27/4.02  
% 10.27/4.02  Inference rules
% 10.27/4.02  ----------------------
% 10.27/4.02  #Ref     : 0
% 10.27/4.02  #Sup     : 1778
% 10.27/4.02  #Fact    : 0
% 10.27/4.02  #Define  : 0
% 10.27/4.02  #Split   : 27
% 10.27/4.02  #Chain   : 0
% 10.27/4.02  #Close   : 0
% 10.27/4.02  
% 10.27/4.02  Ordering : KBO
% 10.27/4.02  
% 10.27/4.02  Simplification rules
% 10.27/4.02  ----------------------
% 10.27/4.02  #Subsume      : 312
% 10.27/4.02  #Demod        : 3426
% 10.27/4.02  #Tautology    : 269
% 10.27/4.02  #SimpNegUnit  : 279
% 10.27/4.02  #BackRed      : 53
% 10.27/4.02  
% 10.27/4.02  #Partial instantiations: 0
% 10.27/4.02  #Strategies tried      : 1
% 10.27/4.02  
% 10.27/4.02  Timing (in seconds)
% 10.27/4.02  ----------------------
% 10.27/4.02  Preprocessing        : 0.37
% 10.27/4.02  Parsing              : 0.19
% 10.27/4.02  CNF conversion       : 0.02
% 10.27/4.02  Main loop            : 2.82
% 10.27/4.02  Inferencing          : 0.68
% 10.27/4.02  Reduction            : 1.43
% 10.27/4.02  Demodulation         : 1.17
% 10.27/4.02  BG Simplification    : 0.06
% 10.27/4.02  Subsumption          : 0.52
% 10.27/4.02  Abstraction          : 0.12
% 10.27/4.02  MUC search           : 0.00
% 10.27/4.02  Cooper               : 0.00
% 10.27/4.02  Total                : 3.23
% 10.27/4.02  Index Insertion      : 0.00
% 10.27/4.02  Index Deletion       : 0.00
% 10.27/4.02  Index Matching       : 0.00
% 10.27/4.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
