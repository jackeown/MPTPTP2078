%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:17 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 120 expanded)
%              Number of leaves         :   36 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 330 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_51,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_67,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_71,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_67])).

tff(c_73,plain,(
    ! [B_48,A_49] :
      ( k1_relat_1(B_48) = A_49
      | ~ v1_partfun1(B_48,A_49)
      | ~ v4_relat_1(B_48,A_49)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_79,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_76])).

tff(c_80,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_210,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_partfun1(C_78,A_79)
      | ~ v1_funct_2(C_78,A_79,B_80)
      | ~ v1_funct_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | v1_xboole_0(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_216,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_210])).

tff(c_220,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_216])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_80,c_220])).

tff(c_223,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_245,plain,(
    ! [A_84,B_85] :
      ( k10_relat_1(A_84,k1_relat_1(B_85)) = k1_relat_1(k5_relat_1(A_84,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_254,plain,(
    ! [A_84] :
      ( k1_relat_1(k5_relat_1(A_84,'#skF_2')) = k10_relat_1(A_84,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_245])).

tff(c_259,plain,(
    ! [A_86] :
      ( k1_relat_1(k5_relat_1(A_86,'#skF_2')) = k10_relat_1(A_86,'#skF_1')
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_254])).

tff(c_36,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_271,plain,
    ( k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_36])).

tff(c_277,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_271])).

tff(c_40,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_327,plain,(
    ! [B_102,A_103] :
      ( m1_subset_1(B_102,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_102),A_103)))
      | ~ r1_tarski(k2_relat_1(B_102),A_103)
      | ~ v1_funct_1(B_102)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k1_relset_1(A_12,B_13,C_14) = k1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_496,plain,(
    ! [B_123,A_124] :
      ( k1_relset_1(k1_relat_1(B_123),A_124,B_123) = k1_relat_1(B_123)
      | ~ r1_tarski(k2_relat_1(B_123),A_124)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_327,c_14])).

tff(c_499,plain,(
    ! [B_2,A_1] :
      ( k1_relset_1(k1_relat_1(B_2),A_1,B_2) = k1_relat_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_496])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( k8_relset_1(A_15,B_16,C_17,D_18) = k10_relat_1(C_17,D_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_517,plain,(
    ! [B_127,A_128,D_129] :
      ( k8_relset_1(k1_relat_1(B_127),A_128,B_127,D_129) = k10_relat_1(B_127,D_129)
      | ~ r1_tarski(k2_relat_1(B_127),A_128)
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_327,c_16])).

tff(c_520,plain,(
    ! [B_2,A_1,D_129] :
      ( k8_relset_1(k1_relat_1(B_2),A_1,B_2,D_129) = k10_relat_1(B_2,D_129)
      | ~ v1_funct_1(B_2)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_517])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( k8_relset_1(A_19,B_20,C_21,B_20) = k1_relset_1(A_19,B_20,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_538,plain,(
    ! [B_133,A_134] :
      ( k8_relset_1(k1_relat_1(B_133),A_134,B_133,A_134) = k1_relset_1(k1_relat_1(B_133),A_134,B_133)
      | ~ r1_tarski(k2_relat_1(B_133),A_134)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_327,c_18])).

tff(c_542,plain,(
    ! [B_135,A_136] :
      ( k8_relset_1(k1_relat_1(B_135),A_136,B_135,A_136) = k1_relset_1(k1_relat_1(B_135),A_136,B_135)
      | ~ v1_funct_1(B_135)
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_4,c_538])).

tff(c_664,plain,(
    ! [B_148,D_149] :
      ( k1_relset_1(k1_relat_1(B_148),D_149,B_148) = k10_relat_1(B_148,D_149)
      | ~ v1_funct_1(B_148)
      | ~ v5_relat_1(B_148,D_149)
      | ~ v1_relat_1(B_148)
      | ~ v1_funct_1(B_148)
      | ~ v5_relat_1(B_148,D_149)
      | ~ v1_relat_1(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_542])).

tff(c_709,plain,(
    ! [B_154,A_155] :
      ( k10_relat_1(B_154,A_155) = k1_relat_1(B_154)
      | ~ v1_funct_1(B_154)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(B_154)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(B_154)
      | ~ v5_relat_1(B_154,A_155)
      | ~ v1_relat_1(B_154) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_664])).

tff(c_713,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_709])).

tff(c_719,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_713])).

tff(c_721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.45  
% 2.99/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.45  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.99/1.45  
% 2.99/1.45  %Foreground sorts:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Background operators:
% 2.99/1.45  
% 2.99/1.45  
% 2.99/1.45  %Foreground operators:
% 2.99/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.99/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.99/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.45  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.99/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.99/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.45  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.99/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.99/1.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.99/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.99/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.99/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.99/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.45  
% 2.99/1.47  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.99/1.47  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.99/1.47  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.99/1.47  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.99/1.47  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.99/1.47  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.99/1.47  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.99/1.47  tff(f_96, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 2.99/1.47  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.99/1.47  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.99/1.47  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 2.99/1.47  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_51, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.99/1.47  tff(c_55, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.99/1.47  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_67, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.47  tff(c_71, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_67])).
% 2.99/1.47  tff(c_73, plain, (![B_48, A_49]: (k1_relat_1(B_48)=A_49 | ~v1_partfun1(B_48, A_49) | ~v4_relat_1(B_48, A_49) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.99/1.47  tff(c_76, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_71, c_73])).
% 2.99/1.47  tff(c_79, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_76])).
% 2.99/1.47  tff(c_80, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_79])).
% 2.99/1.47  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_46, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_210, plain, (![C_78, A_79, B_80]: (v1_partfun1(C_78, A_79) | ~v1_funct_2(C_78, A_79, B_80) | ~v1_funct_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | v1_xboole_0(B_80))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.99/1.47  tff(c_216, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_210])).
% 2.99/1.47  tff(c_220, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_216])).
% 2.99/1.47  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_80, c_220])).
% 2.99/1.47  tff(c_223, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_79])).
% 2.99/1.47  tff(c_245, plain, (![A_84, B_85]: (k10_relat_1(A_84, k1_relat_1(B_85))=k1_relat_1(k5_relat_1(A_84, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.99/1.47  tff(c_254, plain, (![A_84]: (k1_relat_1(k5_relat_1(A_84, '#skF_2'))=k10_relat_1(A_84, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_223, c_245])).
% 2.99/1.47  tff(c_259, plain, (![A_86]: (k1_relat_1(k5_relat_1(A_86, '#skF_2'))=k10_relat_1(A_86, '#skF_1') | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_254])).
% 2.99/1.47  tff(c_36, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_271, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_259, c_36])).
% 2.99/1.47  tff(c_277, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_271])).
% 2.99/1.47  tff(c_40, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.99/1.47  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.47  tff(c_327, plain, (![B_102, A_103]: (m1_subset_1(B_102, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_102), A_103))) | ~r1_tarski(k2_relat_1(B_102), A_103) | ~v1_funct_1(B_102) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.99/1.47  tff(c_14, plain, (![A_12, B_13, C_14]: (k1_relset_1(A_12, B_13, C_14)=k1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.47  tff(c_496, plain, (![B_123, A_124]: (k1_relset_1(k1_relat_1(B_123), A_124, B_123)=k1_relat_1(B_123) | ~r1_tarski(k2_relat_1(B_123), A_124) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_327, c_14])).
% 2.99/1.47  tff(c_499, plain, (![B_2, A_1]: (k1_relset_1(k1_relat_1(B_2), A_1, B_2)=k1_relat_1(B_2) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_496])).
% 2.99/1.47  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (k8_relset_1(A_15, B_16, C_17, D_18)=k10_relat_1(C_17, D_18) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.47  tff(c_517, plain, (![B_127, A_128, D_129]: (k8_relset_1(k1_relat_1(B_127), A_128, B_127, D_129)=k10_relat_1(B_127, D_129) | ~r1_tarski(k2_relat_1(B_127), A_128) | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_327, c_16])).
% 2.99/1.47  tff(c_520, plain, (![B_2, A_1, D_129]: (k8_relset_1(k1_relat_1(B_2), A_1, B_2, D_129)=k10_relat_1(B_2, D_129) | ~v1_funct_1(B_2) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(resolution, [status(thm)], [c_4, c_517])).
% 2.99/1.47  tff(c_18, plain, (![A_19, B_20, C_21]: (k8_relset_1(A_19, B_20, C_21, B_20)=k1_relset_1(A_19, B_20, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.99/1.47  tff(c_538, plain, (![B_133, A_134]: (k8_relset_1(k1_relat_1(B_133), A_134, B_133, A_134)=k1_relset_1(k1_relat_1(B_133), A_134, B_133) | ~r1_tarski(k2_relat_1(B_133), A_134) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_327, c_18])).
% 2.99/1.47  tff(c_542, plain, (![B_135, A_136]: (k8_relset_1(k1_relat_1(B_135), A_136, B_135, A_136)=k1_relset_1(k1_relat_1(B_135), A_136, B_135) | ~v1_funct_1(B_135) | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_4, c_538])).
% 2.99/1.47  tff(c_664, plain, (![B_148, D_149]: (k1_relset_1(k1_relat_1(B_148), D_149, B_148)=k10_relat_1(B_148, D_149) | ~v1_funct_1(B_148) | ~v5_relat_1(B_148, D_149) | ~v1_relat_1(B_148) | ~v1_funct_1(B_148) | ~v5_relat_1(B_148, D_149) | ~v1_relat_1(B_148))), inference(superposition, [status(thm), theory('equality')], [c_520, c_542])).
% 2.99/1.47  tff(c_709, plain, (![B_154, A_155]: (k10_relat_1(B_154, A_155)=k1_relat_1(B_154) | ~v1_funct_1(B_154) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154) | ~v1_funct_1(B_154) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154) | ~v1_funct_1(B_154) | ~v5_relat_1(B_154, A_155) | ~v1_relat_1(B_154))), inference(superposition, [status(thm), theory('equality')], [c_499, c_664])).
% 2.99/1.47  tff(c_713, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_709])).
% 2.99/1.47  tff(c_719, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_713])).
% 2.99/1.47  tff(c_721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_277, c_719])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 151
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 2
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 10
% 2.99/1.47  #Demod        : 99
% 2.99/1.47  #Tautology    : 62
% 2.99/1.47  #SimpNegUnit  : 5
% 2.99/1.47  #BackRed      : 0
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 2.99/1.47  Preprocessing        : 0.31
% 2.99/1.47  Parsing              : 0.16
% 2.99/1.47  CNF conversion       : 0.02
% 2.99/1.47  Main loop            : 0.34
% 2.99/1.47  Inferencing          : 0.14
% 2.99/1.47  Reduction            : 0.10
% 2.99/1.47  Demodulation         : 0.07
% 2.99/1.47  BG Simplification    : 0.02
% 2.99/1.47  Subsumption          : 0.05
% 2.99/1.47  Abstraction          : 0.02
% 2.99/1.47  MUC search           : 0.00
% 2.99/1.47  Cooper               : 0.00
% 2.99/1.47  Total                : 0.69
% 2.99/1.47  Index Insertion      : 0.00
% 2.99/1.47  Index Deletion       : 0.00
% 2.99/1.47  Index Matching       : 0.00
% 2.99/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
