%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:24 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :  207 (3447 expanded)
%              Number of leaves         :   29 (1016 expanded)
%              Depth                    :   16
%              Number of atoms          :  375 (15289 expanded)
%              Number of equality atoms :  138 (6027 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
                & k2_relset_1(A,B,D) = B )
             => ( ( C = k1_xboole_0
                  & B != k1_xboole_0 )
                | ( v2_funct_1(D)
                  & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

tff(c_26,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_389,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_46,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_51,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_51])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_51])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_36,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_79,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_79])).

tff(c_111,plain,(
    ! [B_42,A_43,C_44] :
      ( k1_xboole_0 = B_42
      | k1_relset_1(A_43,B_42,C_44) = A_43
      | ~ v1_funct_2(C_44,A_43,B_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_123,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_87,c_117])).

tff(c_124,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_123])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_60,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_60])).

tff(c_68,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_63])).

tff(c_146,plain,(
    ! [F_49,E_51,B_50,D_53,A_52,C_54] :
      ( k1_partfun1(A_52,B_50,C_54,D_53,E_51,F_49) = k5_relat_1(E_51,F_49)
      | ~ m1_subset_1(F_49,k1_zfmisc_1(k2_zfmisc_1(C_54,D_53)))
      | ~ v1_funct_1(F_49)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(E_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_150,plain,(
    ! [A_52,B_50,E_51] :
      ( k1_partfun1(A_52,B_50,'#skF_2','#skF_3',E_51,'#skF_5') = k5_relat_1(E_51,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50)))
      | ~ v1_funct_1(E_51) ) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_178,plain,(
    ! [A_58,B_59,E_60] :
      ( k1_partfun1(A_58,B_59,'#skF_2','#skF_3',E_60,'#skF_5') = k5_relat_1(E_60,'#skF_5')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_1(E_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_150])).

tff(c_181,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_178])).

tff(c_187,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_32,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_191,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_32])).

tff(c_4,plain,(
    ! [B_3,A_1] :
      ( v2_funct_1(B_3)
      | k2_relat_1(B_3) != k1_relat_1(A_1)
      | ~ v2_funct_1(k5_relat_1(B_3,A_1))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_201,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_207,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_38,c_58,c_44,c_124,c_68,c_201])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_207])).

tff(c_210,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_216,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_224,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_216])).

tff(c_223,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_216])).

tff(c_226,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_234,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_226])).

tff(c_264,plain,(
    ! [B_77,A_78,C_79] :
      ( k1_xboole_0 = B_77
      | k1_relset_1(A_78,B_77,C_79) = A_78
      | ~ v1_funct_2(C_79,A_78,B_77)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_264])).

tff(c_276,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_234,c_270])).

tff(c_277,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_276])).

tff(c_243,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_246,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_243])).

tff(c_251,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_246])).

tff(c_312,plain,(
    ! [C_92,B_88,D_91,F_87,E_89,A_90] :
      ( k1_partfun1(A_90,B_88,C_92,D_91,E_89,F_87) = k5_relat_1(E_89,F_87)
      | ~ m1_subset_1(F_87,k1_zfmisc_1(k2_zfmisc_1(C_92,D_91)))
      | ~ v1_funct_1(F_87)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_316,plain,(
    ! [A_90,B_88,E_89] :
      ( k1_partfun1(A_90,B_88,'#skF_2','#skF_3',E_89,'#skF_5') = k5_relat_1(E_89,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_90,B_88)))
      | ~ v1_funct_1(E_89) ) ),
    inference(resolution,[status(thm)],[c_34,c_312])).

tff(c_344,plain,(
    ! [A_96,B_97,E_98] :
      ( k1_partfun1(A_96,B_97,'#skF_2','#skF_3',E_98,'#skF_5') = k5_relat_1(E_98,'#skF_5')
      | ~ m1_subset_1(E_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ v1_funct_1(E_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_316])).

tff(c_347,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_353,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_347])).

tff(c_357,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_32])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( v2_funct_1(A_1)
      | k2_relat_1(B_3) != k1_relat_1(A_1)
      | ~ v2_funct_1(k5_relat_1(B_3,A_1))
      | ~ v1_funct_1(B_3)
      | ~ v1_relat_1(B_3)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_364,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_357,c_2])).

tff(c_370,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_38,c_223,c_44,c_277,c_251,c_364])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_370])).

tff(c_374,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_373,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_379,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_373])).

tff(c_396,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_34])).

tff(c_399,plain,(
    ! [C_99,A_100,B_101] :
      ( v1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_407,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_399])).

tff(c_397,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_40])).

tff(c_406,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_399])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_384,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_42])).

tff(c_14,plain,(
    ! [C_15,A_13] :
      ( k1_xboole_0 = C_15
      | ~ v1_funct_2(C_15,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_438,plain,(
    ! [C_109,A_110] :
      ( C_109 = '#skF_3'
      | ~ v1_funct_2(C_109,A_110,'#skF_3')
      | A_110 = '#skF_3'
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_374,c_374,c_14])).

tff(c_441,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_397,c_438])).

tff(c_447,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_441])).

tff(c_452,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_390,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_36])).

tff(c_461,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_390])).

tff(c_428,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_436,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_428])).

tff(c_492,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_436])).

tff(c_459,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_396])).

tff(c_464,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_374])).

tff(c_20,plain,(
    ! [B_14,C_15] :
      ( k1_relset_1(k1_xboole_0,B_14,C_15) = k1_xboole_0
      | ~ v1_funct_2(C_15,k1_xboole_0,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_558,plain,(
    ! [B_116,C_117] :
      ( k1_relset_1('#skF_1',B_116,C_117) = '#skF_1'
      | ~ v1_funct_2(C_117,'#skF_1',B_116)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_116))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_464,c_464,c_464,c_20])).

tff(c_561,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_459,c_558])).

tff(c_567,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_492,c_561])).

tff(c_391,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_30])).

tff(c_410,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_413,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_397,c_410])).

tff(c_418,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_413])).

tff(c_455,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_418])).

tff(c_458,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_397])).

tff(c_623,plain,(
    ! [B_129,E_130,C_133,F_128,D_132,A_131] :
      ( k1_partfun1(A_131,B_129,C_133,D_132,E_130,F_128) = k5_relat_1(E_130,F_128)
      | ~ m1_subset_1(F_128,k1_zfmisc_1(k2_zfmisc_1(C_133,D_132)))
      | ~ v1_funct_1(F_128)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_625,plain,(
    ! [A_131,B_129,E_130] :
      ( k1_partfun1(A_131,B_129,'#skF_1','#skF_1',E_130,'#skF_5') = k5_relat_1(E_130,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(resolution,[status(thm)],[c_459,c_623])).

tff(c_634,plain,(
    ! [A_134,B_135,E_136] :
      ( k1_partfun1(A_134,B_135,'#skF_1','#skF_1',E_136,'#skF_5') = k5_relat_1(E_136,'#skF_5')
      | ~ m1_subset_1(E_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(E_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_625])).

tff(c_640,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_458,c_634])).

tff(c_646,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_640])).

tff(c_398,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_32])).

tff(c_457,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_452,c_452,c_398])).

tff(c_672,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_457])).

tff(c_682,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_672,c_4])).

tff(c_688,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_38,c_406,c_44,c_567,c_455,c_682])).

tff(c_690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_688])).

tff(c_691,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_701,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_691,c_390])).

tff(c_728,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_691,c_436])).

tff(c_699,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_691,c_396])).

tff(c_704,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_374])).

tff(c_718,plain,(
    ! [B_14,C_15] :
      ( k1_relset_1('#skF_4',B_14,C_15) = '#skF_4'
      | ~ v1_funct_2(C_15,'#skF_4',B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_704,c_704,c_704,c_20])).

tff(c_740,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_699,c_718])).

tff(c_752,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_728,c_740])).

tff(c_695,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_418])).

tff(c_698,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_397])).

tff(c_851,plain,(
    ! [C_162,D_161,A_160,F_157,E_159,B_158] :
      ( k1_partfun1(A_160,B_158,C_162,D_161,E_159,F_157) = k5_relat_1(E_159,F_157)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(C_162,D_161)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_158)))
      | ~ v1_funct_1(E_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_855,plain,(
    ! [A_160,B_158,E_159] :
      ( k1_partfun1(A_160,B_158,'#skF_4','#skF_4',E_159,'#skF_5') = k5_relat_1(E_159,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_160,B_158)))
      | ~ v1_funct_1(E_159) ) ),
    inference(resolution,[status(thm)],[c_699,c_851])).

tff(c_883,plain,(
    ! [A_166,B_167,E_168] :
      ( k1_partfun1(A_166,B_167,'#skF_4','#skF_4',E_168,'#skF_5') = k5_relat_1(E_168,'#skF_5')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167)))
      | ~ v1_funct_1(E_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_855])).

tff(c_886,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_698,c_883])).

tff(c_892,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_886])).

tff(c_697,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_691,c_691,c_398])).

tff(c_896,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_697])).

tff(c_903,plain,
    ( v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_896,c_4])).

tff(c_909,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_38,c_406,c_44,c_752,c_695,c_903])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_909])).

tff(c_912,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_921,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_34])).

tff(c_923,plain,(
    ! [C_169,A_170,B_171] :
      ( v1_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_930,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_921,c_923])).

tff(c_920,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_40])).

tff(c_931,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_920,c_923])).

tff(c_970,plain,(
    ! [C_179,A_180] :
      ( C_179 = '#skF_3'
      | ~ v1_funct_2(C_179,A_180,'#skF_3')
      | A_180 = '#skF_3'
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_180,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_374,c_374,c_374,c_14])).

tff(c_976,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_920,c_970])).

tff(c_983,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_976])).

tff(c_984,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_983])).

tff(c_914,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_36])).

tff(c_996,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_984,c_914])).

tff(c_952,plain,(
    ! [A_176,B_177,C_178] :
      ( k1_relset_1(A_176,B_177,C_178) = k1_relat_1(C_178)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_959,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_921,c_952])).

tff(c_987,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_984,c_959])).

tff(c_992,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_984,c_921])).

tff(c_998,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_374])).

tff(c_1048,plain,(
    ! [B_183,C_184] :
      ( k1_relset_1('#skF_1',B_183,C_184) = '#skF_1'
      | ~ v1_funct_2(C_184,'#skF_1',B_183)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_183))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_998,c_998,c_998,c_998,c_20])).

tff(c_1051,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_992,c_1048])).

tff(c_1054,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_987,c_1051])).

tff(c_915,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_30])).

tff(c_934,plain,(
    ! [A_173,B_174,C_175] :
      ( k2_relset_1(A_173,B_174,C_175) = k2_relat_1(C_175)
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_940,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_920,c_934])).

tff(c_943,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_940])).

tff(c_989,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_943])).

tff(c_993,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_920])).

tff(c_1158,plain,(
    ! [D_204,A_203,E_202,C_205,B_201,F_200] :
      ( k1_partfun1(A_203,B_201,C_205,D_204,E_202,F_200) = k5_relat_1(E_202,F_200)
      | ~ m1_subset_1(F_200,k1_zfmisc_1(k2_zfmisc_1(C_205,D_204)))
      | ~ v1_funct_1(F_200)
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1162,plain,(
    ! [A_203,B_201,E_202] :
      ( k1_partfun1(A_203,B_201,'#skF_1','#skF_1',E_202,'#skF_5') = k5_relat_1(E_202,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_201)))
      | ~ v1_funct_1(E_202) ) ),
    inference(resolution,[status(thm)],[c_992,c_1158])).

tff(c_1190,plain,(
    ! [A_209,B_210,E_211] :
      ( k1_partfun1(A_209,B_210,'#skF_1','#skF_1',E_211,'#skF_5') = k5_relat_1(E_211,'#skF_5')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_1(E_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1162])).

tff(c_1193,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_993,c_1190])).

tff(c_1199,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1193])).

tff(c_922,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_379,c_32])).

tff(c_991,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_984,c_984,c_922])).

tff(c_1203,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_991])).

tff(c_1210,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1203,c_2])).

tff(c_1216,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_38,c_931,c_44,c_1054,c_989,c_1210])).

tff(c_1218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_1216])).

tff(c_1219,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_983])).

tff(c_1232,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_914])).

tff(c_1228,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_921])).

tff(c_1234,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_374])).

tff(c_1256,plain,(
    ! [B_14,C_15] :
      ( k1_relset_1('#skF_4',B_14,C_15) = '#skF_4'
      | ~ v1_funct_2(C_15,'#skF_4',B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_14))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1234,c_1234,c_1234,c_20])).

tff(c_1268,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1228,c_1256])).

tff(c_1280,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_1268])).

tff(c_1223,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_959])).

tff(c_1305,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_1223])).

tff(c_1225,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_943])).

tff(c_1229,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_920])).

tff(c_1375,plain,(
    ! [C_234,A_232,F_229,D_233,E_231,B_230] :
      ( k1_partfun1(A_232,B_230,C_234,D_233,E_231,F_229) = k5_relat_1(E_231,F_229)
      | ~ m1_subset_1(F_229,k1_zfmisc_1(k2_zfmisc_1(C_234,D_233)))
      | ~ v1_funct_1(F_229)
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1379,plain,(
    ! [A_232,B_230,E_231] :
      ( k1_partfun1(A_232,B_230,'#skF_4','#skF_4',E_231,'#skF_5') = k5_relat_1(E_231,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_231,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_231) ) ),
    inference(resolution,[status(thm)],[c_1228,c_1375])).

tff(c_1407,plain,(
    ! [A_238,B_239,E_240] :
      ( k1_partfun1(A_238,B_239,'#skF_4','#skF_4',E_240,'#skF_5') = k5_relat_1(E_240,'#skF_5')
      | ~ m1_subset_1(E_240,k1_zfmisc_1(k2_zfmisc_1(A_238,B_239)))
      | ~ v1_funct_1(E_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1379])).

tff(c_1410,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1229,c_1407])).

tff(c_1416,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1410])).

tff(c_1227,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1219,c_1219,c_1219,c_922])).

tff(c_1420,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1416,c_1227])).

tff(c_1427,plain,
    ( v2_funct_1('#skF_5')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1420,c_2])).

tff(c_1433,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_38,c_931,c_44,c_1305,c_1225,c_1427])).

tff(c_1435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_1433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.53  
% 3.43/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.54  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.43/1.54  
% 3.43/1.54  %Foreground sorts:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Background operators:
% 3.43/1.54  
% 3.43/1.54  
% 3.43/1.54  %Foreground operators:
% 3.43/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.43/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.43/1.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.43/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.43/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.43/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.43/1.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.43/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.43/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.43/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.43/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.43/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.43/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.43/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.43/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.43/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.43/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.43/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.43/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.43/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.43/1.54  
% 3.43/1.57  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 3.43/1.57  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.43/1.57  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.57  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.43/1.57  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.43/1.57  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.43/1.57  tff(f_42, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_1)).
% 3.43/1.57  tff(c_26, plain, (~v2_funct_1('#skF_5') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_389, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 3.43/1.57  tff(c_46, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 3.43/1.57  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_51, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.57  tff(c_59, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_51])).
% 3.43/1.57  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_51])).
% 3.43/1.57  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_28, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_45, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_28])).
% 3.43/1.57  tff(c_36, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_79, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.57  tff(c_87, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_79])).
% 3.43/1.57  tff(c_111, plain, (![B_42, A_43, C_44]: (k1_xboole_0=B_42 | k1_relset_1(A_43, B_42, C_44)=A_43 | ~v1_funct_2(C_44, A_43, B_42) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.57  tff(c_117, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_111])).
% 3.43/1.57  tff(c_123, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_87, c_117])).
% 3.43/1.57  tff(c_124, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_45, c_123])).
% 3.43/1.57  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_60, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.43/1.57  tff(c_63, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_60])).
% 3.43/1.57  tff(c_68, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_63])).
% 3.43/1.57  tff(c_146, plain, (![F_49, E_51, B_50, D_53, A_52, C_54]: (k1_partfun1(A_52, B_50, C_54, D_53, E_51, F_49)=k5_relat_1(E_51, F_49) | ~m1_subset_1(F_49, k1_zfmisc_1(k2_zfmisc_1(C_54, D_53))) | ~v1_funct_1(F_49) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_50))) | ~v1_funct_1(E_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_150, plain, (![A_52, B_50, E_51]: (k1_partfun1(A_52, B_50, '#skF_2', '#skF_3', E_51, '#skF_5')=k5_relat_1(E_51, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_50))) | ~v1_funct_1(E_51))), inference(resolution, [status(thm)], [c_34, c_146])).
% 3.43/1.57  tff(c_178, plain, (![A_58, B_59, E_60]: (k1_partfun1(A_58, B_59, '#skF_2', '#skF_3', E_60, '#skF_5')=k5_relat_1(E_60, '#skF_5') | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_1(E_60))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_150])).
% 3.43/1.57  tff(c_181, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_178])).
% 3.43/1.57  tff(c_187, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_181])).
% 3.43/1.57  tff(c_32, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_191, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_32])).
% 3.43/1.57  tff(c_4, plain, (![B_3, A_1]: (v2_funct_1(B_3) | k2_relat_1(B_3)!=k1_relat_1(A_1) | ~v2_funct_1(k5_relat_1(B_3, A_1)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.43/1.57  tff(c_201, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_191, c_4])).
% 3.43/1.57  tff(c_207, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_38, c_58, c_44, c_124, c_68, c_201])).
% 3.43/1.57  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_207])).
% 3.43/1.57  tff(c_210, plain, (~v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 3.43/1.57  tff(c_216, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.57  tff(c_224, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_216])).
% 3.43/1.57  tff(c_223, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_216])).
% 3.43/1.57  tff(c_226, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.57  tff(c_234, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_34, c_226])).
% 3.43/1.57  tff(c_264, plain, (![B_77, A_78, C_79]: (k1_xboole_0=B_77 | k1_relset_1(A_78, B_77, C_79)=A_78 | ~v1_funct_2(C_79, A_78, B_77) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.57  tff(c_270, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_264])).
% 3.43/1.57  tff(c_276, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_234, c_270])).
% 3.43/1.57  tff(c_277, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_45, c_276])).
% 3.43/1.57  tff(c_243, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.43/1.57  tff(c_246, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_243])).
% 3.43/1.57  tff(c_251, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_246])).
% 3.43/1.57  tff(c_312, plain, (![C_92, B_88, D_91, F_87, E_89, A_90]: (k1_partfun1(A_90, B_88, C_92, D_91, E_89, F_87)=k5_relat_1(E_89, F_87) | ~m1_subset_1(F_87, k1_zfmisc_1(k2_zfmisc_1(C_92, D_91))) | ~v1_funct_1(F_87) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_88))) | ~v1_funct_1(E_89))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_316, plain, (![A_90, B_88, E_89]: (k1_partfun1(A_90, B_88, '#skF_2', '#skF_3', E_89, '#skF_5')=k5_relat_1(E_89, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_90, B_88))) | ~v1_funct_1(E_89))), inference(resolution, [status(thm)], [c_34, c_312])).
% 3.43/1.57  tff(c_344, plain, (![A_96, B_97, E_98]: (k1_partfun1(A_96, B_97, '#skF_2', '#skF_3', E_98, '#skF_5')=k5_relat_1(E_98, '#skF_5') | ~m1_subset_1(E_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~v1_funct_1(E_98))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_316])).
% 3.43/1.57  tff(c_347, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_344])).
% 3.43/1.57  tff(c_353, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_347])).
% 3.43/1.57  tff(c_357, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_353, c_32])).
% 3.43/1.57  tff(c_2, plain, (![A_1, B_3]: (v2_funct_1(A_1) | k2_relat_1(B_3)!=k1_relat_1(A_1) | ~v2_funct_1(k5_relat_1(B_3, A_1)) | ~v1_funct_1(B_3) | ~v1_relat_1(B_3) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.43/1.57  tff(c_364, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_357, c_2])).
% 3.43/1.57  tff(c_370, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_224, c_38, c_223, c_44, c_277, c_251, c_364])).
% 3.43/1.57  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_210, c_370])).
% 3.43/1.57  tff(c_374, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 3.43/1.57  tff(c_373, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 3.43/1.57  tff(c_379, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_374, c_373])).
% 3.43/1.57  tff(c_396, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_34])).
% 3.43/1.57  tff(c_399, plain, (![C_99, A_100, B_101]: (v1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.57  tff(c_407, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_396, c_399])).
% 3.43/1.57  tff(c_397, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_40])).
% 3.43/1.57  tff(c_406, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_397, c_399])).
% 3.43/1.57  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.43/1.57  tff(c_384, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_42])).
% 3.43/1.57  tff(c_14, plain, (![C_15, A_13]: (k1_xboole_0=C_15 | ~v1_funct_2(C_15, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.57  tff(c_438, plain, (![C_109, A_110]: (C_109='#skF_3' | ~v1_funct_2(C_109, A_110, '#skF_3') | A_110='#skF_3' | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_374, c_374, c_374, c_14])).
% 3.43/1.57  tff(c_441, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_397, c_438])).
% 3.43/1.57  tff(c_447, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_384, c_441])).
% 3.43/1.57  tff(c_452, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_447])).
% 3.43/1.57  tff(c_390, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_36])).
% 3.43/1.57  tff(c_461, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_390])).
% 3.43/1.57  tff(c_428, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.57  tff(c_436, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_396, c_428])).
% 3.43/1.57  tff(c_492, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_436])).
% 3.43/1.57  tff(c_459, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_396])).
% 3.43/1.57  tff(c_464, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_374])).
% 3.43/1.57  tff(c_20, plain, (![B_14, C_15]: (k1_relset_1(k1_xboole_0, B_14, C_15)=k1_xboole_0 | ~v1_funct_2(C_15, k1_xboole_0, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.43/1.57  tff(c_558, plain, (![B_116, C_117]: (k1_relset_1('#skF_1', B_116, C_117)='#skF_1' | ~v1_funct_2(C_117, '#skF_1', B_116) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_116))))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_464, c_464, c_464, c_20])).
% 3.43/1.57  tff(c_561, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_459, c_558])).
% 3.43/1.57  tff(c_567, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_461, c_492, c_561])).
% 3.43/1.57  tff(c_391, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_30])).
% 3.43/1.57  tff(c_410, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.43/1.57  tff(c_413, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_397, c_410])).
% 3.43/1.57  tff(c_418, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_391, c_413])).
% 3.43/1.57  tff(c_455, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_418])).
% 3.43/1.57  tff(c_458, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_397])).
% 3.43/1.57  tff(c_623, plain, (![B_129, E_130, C_133, F_128, D_132, A_131]: (k1_partfun1(A_131, B_129, C_133, D_132, E_130, F_128)=k5_relat_1(E_130, F_128) | ~m1_subset_1(F_128, k1_zfmisc_1(k2_zfmisc_1(C_133, D_132))) | ~v1_funct_1(F_128) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_129))) | ~v1_funct_1(E_130))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_625, plain, (![A_131, B_129, E_130]: (k1_partfun1(A_131, B_129, '#skF_1', '#skF_1', E_130, '#skF_5')=k5_relat_1(E_130, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_129))) | ~v1_funct_1(E_130))), inference(resolution, [status(thm)], [c_459, c_623])).
% 3.43/1.57  tff(c_634, plain, (![A_134, B_135, E_136]: (k1_partfun1(A_134, B_135, '#skF_1', '#skF_1', E_136, '#skF_5')=k5_relat_1(E_136, '#skF_5') | ~m1_subset_1(E_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(E_136))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_625])).
% 3.43/1.57  tff(c_640, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_458, c_634])).
% 3.43/1.57  tff(c_646, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_640])).
% 3.43/1.57  tff(c_398, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_32])).
% 3.43/1.57  tff(c_457, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_452, c_452, c_452, c_398])).
% 3.43/1.57  tff(c_672, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_457])).
% 3.43/1.57  tff(c_682, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_672, c_4])).
% 3.43/1.57  tff(c_688, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_38, c_406, c_44, c_567, c_455, c_682])).
% 3.43/1.57  tff(c_690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_688])).
% 3.43/1.57  tff(c_691, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_447])).
% 3.43/1.57  tff(c_701, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_691, c_691, c_390])).
% 3.43/1.57  tff(c_728, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_691, c_691, c_436])).
% 3.43/1.57  tff(c_699, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_691, c_691, c_396])).
% 3.43/1.57  tff(c_704, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_691, c_374])).
% 3.43/1.57  tff(c_718, plain, (![B_14, C_15]: (k1_relset_1('#skF_4', B_14, C_15)='#skF_4' | ~v1_funct_2(C_15, '#skF_4', B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_704, c_704, c_704, c_20])).
% 3.43/1.57  tff(c_740, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_699, c_718])).
% 3.43/1.57  tff(c_752, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_701, c_728, c_740])).
% 3.43/1.57  tff(c_695, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_691, c_418])).
% 3.43/1.57  tff(c_698, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_691, c_397])).
% 3.43/1.57  tff(c_851, plain, (![C_162, D_161, A_160, F_157, E_159, B_158]: (k1_partfun1(A_160, B_158, C_162, D_161, E_159, F_157)=k5_relat_1(E_159, F_157) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(C_162, D_161))) | ~v1_funct_1(F_157) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_158))) | ~v1_funct_1(E_159))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_855, plain, (![A_160, B_158, E_159]: (k1_partfun1(A_160, B_158, '#skF_4', '#skF_4', E_159, '#skF_5')=k5_relat_1(E_159, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_160, B_158))) | ~v1_funct_1(E_159))), inference(resolution, [status(thm)], [c_699, c_851])).
% 3.43/1.57  tff(c_883, plain, (![A_166, B_167, E_168]: (k1_partfun1(A_166, B_167, '#skF_4', '#skF_4', E_168, '#skF_5')=k5_relat_1(E_168, '#skF_5') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))) | ~v1_funct_1(E_168))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_855])).
% 3.43/1.57  tff(c_886, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_698, c_883])).
% 3.43/1.57  tff(c_892, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_886])).
% 3.43/1.57  tff(c_697, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_691, c_691, c_691, c_398])).
% 3.43/1.57  tff(c_896, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_892, c_697])).
% 3.43/1.57  tff(c_903, plain, (v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_896, c_4])).
% 3.43/1.57  tff(c_909, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_38, c_406, c_44, c_752, c_695, c_903])).
% 3.43/1.57  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_909])).
% 3.43/1.57  tff(c_912, plain, (~v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 3.43/1.57  tff(c_921, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_34])).
% 3.43/1.57  tff(c_923, plain, (![C_169, A_170, B_171]: (v1_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.43/1.57  tff(c_930, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_921, c_923])).
% 3.43/1.57  tff(c_920, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_40])).
% 3.43/1.57  tff(c_931, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_920, c_923])).
% 3.43/1.57  tff(c_970, plain, (![C_179, A_180]: (C_179='#skF_3' | ~v1_funct_2(C_179, A_180, '#skF_3') | A_180='#skF_3' | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_180, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_374, c_374, c_374, c_14])).
% 3.43/1.57  tff(c_976, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_920, c_970])).
% 3.43/1.57  tff(c_983, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_384, c_976])).
% 3.43/1.57  tff(c_984, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_983])).
% 3.43/1.57  tff(c_914, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_379, c_36])).
% 3.43/1.57  tff(c_996, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_984, c_914])).
% 3.43/1.57  tff(c_952, plain, (![A_176, B_177, C_178]: (k1_relset_1(A_176, B_177, C_178)=k1_relat_1(C_178) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.57  tff(c_959, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_921, c_952])).
% 3.43/1.57  tff(c_987, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_984, c_959])).
% 3.43/1.57  tff(c_992, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_984, c_921])).
% 3.43/1.57  tff(c_998, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_984, c_374])).
% 3.43/1.57  tff(c_1048, plain, (![B_183, C_184]: (k1_relset_1('#skF_1', B_183, C_184)='#skF_1' | ~v1_funct_2(C_184, '#skF_1', B_183) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_183))))), inference(demodulation, [status(thm), theory('equality')], [c_998, c_998, c_998, c_998, c_20])).
% 3.43/1.57  tff(c_1051, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_992, c_1048])).
% 3.43/1.57  tff(c_1054, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_996, c_987, c_1051])).
% 3.43/1.57  tff(c_915, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_30])).
% 3.43/1.57  tff(c_934, plain, (![A_173, B_174, C_175]: (k2_relset_1(A_173, B_174, C_175)=k2_relat_1(C_175) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_173, B_174))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.43/1.57  tff(c_940, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_920, c_934])).
% 3.43/1.57  tff(c_943, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_940])).
% 3.43/1.57  tff(c_989, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_984, c_943])).
% 3.43/1.57  tff(c_993, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_920])).
% 3.43/1.57  tff(c_1158, plain, (![D_204, A_203, E_202, C_205, B_201, F_200]: (k1_partfun1(A_203, B_201, C_205, D_204, E_202, F_200)=k5_relat_1(E_202, F_200) | ~m1_subset_1(F_200, k1_zfmisc_1(k2_zfmisc_1(C_205, D_204))) | ~v1_funct_1(F_200) | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_202))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_1162, plain, (![A_203, B_201, E_202]: (k1_partfun1(A_203, B_201, '#skF_1', '#skF_1', E_202, '#skF_5')=k5_relat_1(E_202, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_201))) | ~v1_funct_1(E_202))), inference(resolution, [status(thm)], [c_992, c_1158])).
% 3.43/1.57  tff(c_1190, plain, (![A_209, B_210, E_211]: (k1_partfun1(A_209, B_210, '#skF_1', '#skF_1', E_211, '#skF_5')=k5_relat_1(E_211, '#skF_5') | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_1(E_211))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1162])).
% 3.43/1.57  tff(c_1193, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_993, c_1190])).
% 3.43/1.57  tff(c_1199, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1193])).
% 3.43/1.57  tff(c_922, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_379, c_379, c_32])).
% 3.43/1.57  tff(c_991, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_984, c_984, c_984, c_922])).
% 3.43/1.57  tff(c_1203, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_991])).
% 3.43/1.57  tff(c_1210, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1203, c_2])).
% 3.43/1.57  tff(c_1216, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_38, c_931, c_44, c_1054, c_989, c_1210])).
% 3.43/1.57  tff(c_1218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_1216])).
% 3.43/1.57  tff(c_1219, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_983])).
% 3.43/1.57  tff(c_1232, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_914])).
% 3.43/1.57  tff(c_1228, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_921])).
% 3.43/1.57  tff(c_1234, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_374])).
% 3.43/1.57  tff(c_1256, plain, (![B_14, C_15]: (k1_relset_1('#skF_4', B_14, C_15)='#skF_4' | ~v1_funct_2(C_15, '#skF_4', B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_14))))), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1234, c_1234, c_1234, c_20])).
% 3.43/1.57  tff(c_1268, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1228, c_1256])).
% 3.43/1.57  tff(c_1280, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_1268])).
% 3.43/1.57  tff(c_1223, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_959])).
% 3.43/1.57  tff(c_1305, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_1223])).
% 3.43/1.57  tff(c_1225, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_943])).
% 3.43/1.57  tff(c_1229, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_920])).
% 3.43/1.57  tff(c_1375, plain, (![C_234, A_232, F_229, D_233, E_231, B_230]: (k1_partfun1(A_232, B_230, C_234, D_233, E_231, F_229)=k5_relat_1(E_231, F_229) | ~m1_subset_1(F_229, k1_zfmisc_1(k2_zfmisc_1(C_234, D_233))) | ~v1_funct_1(F_229) | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_231))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.43/1.57  tff(c_1379, plain, (![A_232, B_230, E_231]: (k1_partfun1(A_232, B_230, '#skF_4', '#skF_4', E_231, '#skF_5')=k5_relat_1(E_231, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_231, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_231))), inference(resolution, [status(thm)], [c_1228, c_1375])).
% 3.43/1.57  tff(c_1407, plain, (![A_238, B_239, E_240]: (k1_partfun1(A_238, B_239, '#skF_4', '#skF_4', E_240, '#skF_5')=k5_relat_1(E_240, '#skF_5') | ~m1_subset_1(E_240, k1_zfmisc_1(k2_zfmisc_1(A_238, B_239))) | ~v1_funct_1(E_240))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1379])).
% 3.43/1.57  tff(c_1410, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1229, c_1407])).
% 3.43/1.57  tff(c_1416, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1410])).
% 3.43/1.57  tff(c_1227, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1219, c_1219, c_1219, c_922])).
% 3.43/1.57  tff(c_1420, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1416, c_1227])).
% 3.43/1.57  tff(c_1427, plain, (v2_funct_1('#skF_5') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1420, c_2])).
% 3.43/1.57  tff(c_1433, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_930, c_38, c_931, c_44, c_1305, c_1225, c_1427])).
% 3.43/1.57  tff(c_1435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_1433])).
% 3.43/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.57  
% 3.43/1.57  Inference rules
% 3.43/1.57  ----------------------
% 3.43/1.57  #Ref     : 0
% 3.43/1.57  #Sup     : 328
% 3.43/1.57  #Fact    : 0
% 3.43/1.57  #Define  : 0
% 3.43/1.57  #Split   : 7
% 3.43/1.57  #Chain   : 0
% 3.43/1.57  #Close   : 0
% 3.43/1.57  
% 3.43/1.57  Ordering : KBO
% 3.43/1.57  
% 3.43/1.57  Simplification rules
% 3.43/1.57  ----------------------
% 3.43/1.57  #Subsume      : 0
% 3.43/1.57  #Demod        : 405
% 3.43/1.57  #Tautology    : 244
% 3.43/1.57  #SimpNegUnit  : 14
% 3.43/1.57  #BackRed      : 70
% 3.43/1.57  
% 3.43/1.57  #Partial instantiations: 0
% 3.43/1.57  #Strategies tried      : 1
% 3.43/1.57  
% 3.43/1.57  Timing (in seconds)
% 3.43/1.57  ----------------------
% 3.43/1.57  Preprocessing        : 0.31
% 3.43/1.57  Parsing              : 0.17
% 3.43/1.57  CNF conversion       : 0.02
% 3.43/1.57  Main loop            : 0.44
% 3.43/1.57  Inferencing          : 0.16
% 3.43/1.57  Reduction            : 0.15
% 3.43/1.57  Demodulation         : 0.10
% 3.43/1.57  BG Simplification    : 0.02
% 3.43/1.57  Subsumption          : 0.06
% 3.43/1.57  Abstraction          : 0.02
% 3.43/1.57  MUC search           : 0.00
% 3.43/1.57  Cooper               : 0.00
% 3.43/1.57  Total                : 0.83
% 3.43/1.57  Index Insertion      : 0.00
% 3.43/1.57  Index Deletion       : 0.00
% 3.43/1.57  Index Matching       : 0.00
% 3.43/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
