%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:11 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 255 expanded)
%              Number of leaves         :   43 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  161 ( 366 expanded)
%              Number of equality atoms :   70 ( 183 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k6_subset_1(A,B)) = k6_subset_1(k4_relat_1(A),k4_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_32,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k4_xboole_0(A,B),C) = k4_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k4_xboole_0(A,B)) = k4_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_104,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_54,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_105,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_56,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_100,plain,(
    ! [A_61] :
      ( v1_relat_1(A_61)
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_38,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(k5_relat_1(A_44,B_45))
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_155,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_167,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_155])).

tff(c_170,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_167])).

tff(c_30,plain,(
    ! [A_38,B_39] : k6_subset_1(A_38,B_39) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [A_48,B_50] :
      ( k6_subset_1(k4_relat_1(A_48),k4_relat_1(B_50)) = k4_relat_1(k6_subset_1(A_48,B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_582,plain,(
    ! [A_110,B_111] :
      ( k4_xboole_0(k4_relat_1(A_110),k4_relat_1(B_111)) = k4_relat_1(k4_xboole_0(A_110,B_111))
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_44])).

tff(c_589,plain,(
    ! [B_111] :
      ( k4_relat_1(k4_xboole_0(B_111,B_111)) = k1_xboole_0
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_170])).

tff(c_604,plain,(
    ! [B_111] :
      ( k4_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_589])).

tff(c_619,plain,(
    ! [B_114] :
      ( ~ v1_relat_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(splitLeft,[status(thm)],[c_604])).

tff(c_625,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_104,c_619])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_625])).

tff(c_634,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_604])).

tff(c_48,plain,(
    ! [B_56,A_54] :
      ( k5_relat_1(k4_relat_1(B_56),k4_relat_1(A_54)) = k4_relat_1(k5_relat_1(A_54,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_647,plain,(
    ! [B_56] :
      ( k5_relat_1(k4_relat_1(B_56),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_48])).

tff(c_811,plain,(
    ! [B_128] :
      ( k5_relat_1(k4_relat_1(B_128),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,B_128))
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_647])).

tff(c_36,plain,(
    ! [A_43] :
      ( v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_270,plain,(
    ! [C_85,A_86,B_87] : k4_xboole_0(k2_zfmisc_1(C_85,A_86),k2_zfmisc_1(C_85,B_87)) = k2_zfmisc_1(C_85,k4_xboole_0(A_86,B_87)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_277,plain,(
    ! [C_85,B_87] : k2_zfmisc_1(C_85,k4_xboole_0(B_87,B_87)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_170])).

tff(c_286,plain,(
    ! [C_85] : k2_zfmisc_1(C_85,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_277])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_670,plain,(
    ! [B_115,A_116] :
      ( k2_relat_1(k5_relat_1(B_115,A_116)) = k2_relat_1(A_116)
      | ~ r1_tarski(k1_relat_1(A_116),k2_relat_1(B_115))
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_673,plain,(
    ! [B_115] :
      ( k2_relat_1(k5_relat_1(B_115,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_115))
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_670])).

tff(c_681,plain,(
    ! [B_117] :
      ( k2_relat_1(k5_relat_1(B_117,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_10,c_50,c_673])).

tff(c_42,plain,(
    ! [A_47] :
      ( k3_xboole_0(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_693,plain,(
    ! [B_117] :
      ( k3_xboole_0(k5_relat_1(B_117,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_117,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_117,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_117,k1_xboole_0))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_42])).

tff(c_701,plain,(
    ! [B_118] :
      ( k5_relat_1(B_118,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_118,k1_xboole_0))
      | ~ v1_relat_1(B_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_286,c_693])).

tff(c_705,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_38,c_701])).

tff(c_709,plain,(
    ! [A_119] :
      ( k5_relat_1(A_119,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_705])).

tff(c_723,plain,(
    ! [A_43] :
      ( k5_relat_1(k4_relat_1(A_43),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_43) ) ),
    inference(resolution,[status(thm)],[c_36,c_709])).

tff(c_851,plain,(
    ! [B_136] :
      ( k4_relat_1(k5_relat_1(k1_xboole_0,B_136)) = k1_xboole_0
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_723])).

tff(c_40,plain,(
    ! [A_46] :
      ( k4_relat_1(k4_relat_1(A_46)) = A_46
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_878,plain,(
    ! [B_136] :
      ( k5_relat_1(k1_xboole_0,B_136) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_136))
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_851,c_40])).

tff(c_1775,plain,(
    ! [B_161] :
      ( k5_relat_1(k1_xboole_0,B_161) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_161))
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_878])).

tff(c_1785,plain,(
    ! [B_45] :
      ( k5_relat_1(k1_xboole_0,B_45) = k1_xboole_0
      | ~ v1_relat_1(B_45)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_1775])).

tff(c_1791,plain,(
    ! [B_162] :
      ( k5_relat_1(k1_xboole_0,B_162) = k1_xboole_0
      | ~ v1_relat_1(B_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1785])).

tff(c_1812,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_1791])).

tff(c_1823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1812])).

tff(c_1824,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1878,plain,(
    ! [A_171,B_172] : k5_xboole_0(A_171,k3_xboole_0(A_171,B_172)) = k4_xboole_0(A_171,B_172) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1890,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1878])).

tff(c_1893,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1890])).

tff(c_1999,plain,(
    ! [C_186,A_187,B_188] : k4_xboole_0(k2_zfmisc_1(C_186,A_187),k2_zfmisc_1(C_186,B_188)) = k2_zfmisc_1(C_186,k4_xboole_0(A_187,B_188)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2006,plain,(
    ! [C_186,B_188] : k2_zfmisc_1(C_186,k4_xboole_0(B_188,B_188)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_1893])).

tff(c_2015,plain,(
    ! [C_186] : k2_zfmisc_1(C_186,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1893,c_2006])).

tff(c_2491,plain,(
    ! [B_223,A_224] :
      ( k2_relat_1(k5_relat_1(B_223,A_224)) = k2_relat_1(A_224)
      | ~ r1_tarski(k1_relat_1(A_224),k2_relat_1(B_223))
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2494,plain,(
    ! [B_223] :
      ( k2_relat_1(k5_relat_1(B_223,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_223))
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2491])).

tff(c_2502,plain,(
    ! [B_225] :
      ( k2_relat_1(k5_relat_1(B_225,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_10,c_50,c_2494])).

tff(c_2514,plain,(
    ! [B_225] :
      ( k3_xboole_0(k5_relat_1(B_225,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_225,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_225,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_225,k1_xboole_0))
      | ~ v1_relat_1(B_225) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2502,c_42])).

tff(c_2525,plain,(
    ! [B_226] :
      ( k5_relat_1(B_226,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_226,k1_xboole_0))
      | ~ v1_relat_1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2015,c_2514])).

tff(c_2532,plain,(
    ! [A_44] :
      ( k5_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_38,c_2525])).

tff(c_2536,plain,(
    ! [A_227] :
      ( k5_relat_1(A_227,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_2532])).

tff(c_2548,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_2536])).

tff(c_2555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1824,c_2548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:58:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.64  
% 3.94/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.64  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k4_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.94/1.64  
% 3.94/1.64  %Foreground sorts:
% 3.94/1.64  
% 3.94/1.64  
% 3.94/1.64  %Background operators:
% 3.94/1.64  
% 3.94/1.64  
% 3.94/1.64  %Foreground operators:
% 3.94/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.94/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.94/1.64  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.94/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.94/1.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.94/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.94/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.94/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.94/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.94/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.94/1.64  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.94/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.64  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.94/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.94/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.94/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.94/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.94/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.94/1.64  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.94/1.64  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.94/1.64  
% 3.94/1.66  tff(f_111, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.94/1.66  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.94/1.66  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.94/1.66  tff(f_70, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.94/1.66  tff(f_36, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.94/1.66  tff(f_28, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.94/1.66  tff(f_30, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.94/1.66  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.94/1.66  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k6_subset_1(A, B)) = k6_subset_1(k4_relat_1(A), k4_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_relat_1)).
% 3.94/1.66  tff(f_101, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.94/1.66  tff(f_64, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 3.94/1.66  tff(f_32, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.94/1.66  tff(f_52, axiom, (![A, B, C]: ((k2_zfmisc_1(k4_xboole_0(A, B), C) = k4_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k4_xboole_0(A, B)) = k4_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_zfmisc_1)).
% 3.94/1.66  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.94/1.66  tff(f_104, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.94/1.66  tff(f_94, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.94/1.66  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.94/1.66  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 3.94/1.66  tff(c_54, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.94/1.66  tff(c_105, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 3.94/1.66  tff(c_56, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.94/1.66  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.94/1.66  tff(c_100, plain, (![A_61]: (v1_relat_1(A_61) | ~v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.94/1.66  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_100])).
% 3.94/1.66  tff(c_38, plain, (![A_44, B_45]: (v1_relat_1(k5_relat_1(A_44, B_45)) | ~v1_relat_1(B_45) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.94/1.66  tff(c_12, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.94/1.66  tff(c_4, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.94/1.66  tff(c_155, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.94/1.66  tff(c_167, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_155])).
% 3.94/1.66  tff(c_170, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_167])).
% 3.94/1.66  tff(c_30, plain, (![A_38, B_39]: (k6_subset_1(A_38, B_39)=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.94/1.66  tff(c_44, plain, (![A_48, B_50]: (k6_subset_1(k4_relat_1(A_48), k4_relat_1(B_50))=k4_relat_1(k6_subset_1(A_48, B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.94/1.66  tff(c_582, plain, (![A_110, B_111]: (k4_xboole_0(k4_relat_1(A_110), k4_relat_1(B_111))=k4_relat_1(k4_xboole_0(A_110, B_111)) | ~v1_relat_1(B_111) | ~v1_relat_1(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_44])).
% 3.94/1.66  tff(c_589, plain, (![B_111]: (k4_relat_1(k4_xboole_0(B_111, B_111))=k1_xboole_0 | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_582, c_170])).
% 3.94/1.66  tff(c_604, plain, (![B_111]: (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_111) | ~v1_relat_1(B_111))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_589])).
% 3.94/1.66  tff(c_619, plain, (![B_114]: (~v1_relat_1(B_114) | ~v1_relat_1(B_114))), inference(splitLeft, [status(thm)], [c_604])).
% 3.94/1.66  tff(c_625, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_619])).
% 3.94/1.66  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_625])).
% 3.94/1.66  tff(c_634, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_604])).
% 3.94/1.66  tff(c_48, plain, (![B_56, A_54]: (k5_relat_1(k4_relat_1(B_56), k4_relat_1(A_54))=k4_relat_1(k5_relat_1(A_54, B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.94/1.66  tff(c_647, plain, (![B_56]: (k5_relat_1(k4_relat_1(B_56), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_634, c_48])).
% 3.94/1.66  tff(c_811, plain, (![B_128]: (k5_relat_1(k4_relat_1(B_128), k1_xboole_0)=k4_relat_1(k5_relat_1(k1_xboole_0, B_128)) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_647])).
% 3.94/1.66  tff(c_36, plain, (![A_43]: (v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.94/1.66  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.66  tff(c_270, plain, (![C_85, A_86, B_87]: (k4_xboole_0(k2_zfmisc_1(C_85, A_86), k2_zfmisc_1(C_85, B_87))=k2_zfmisc_1(C_85, k4_xboole_0(A_86, B_87)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.66  tff(c_277, plain, (![C_85, B_87]: (k2_zfmisc_1(C_85, k4_xboole_0(B_87, B_87))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_270, c_170])).
% 3.94/1.66  tff(c_286, plain, (![C_85]: (k2_zfmisc_1(C_85, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_170, c_277])).
% 3.94/1.66  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.94/1.66  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.94/1.66  tff(c_52, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.94/1.66  tff(c_670, plain, (![B_115, A_116]: (k2_relat_1(k5_relat_1(B_115, A_116))=k2_relat_1(A_116) | ~r1_tarski(k1_relat_1(A_116), k2_relat_1(B_115)) | ~v1_relat_1(B_115) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.66  tff(c_673, plain, (![B_115]: (k2_relat_1(k5_relat_1(B_115, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_115)) | ~v1_relat_1(B_115) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_670])).
% 3.94/1.66  tff(c_681, plain, (![B_117]: (k2_relat_1(k5_relat_1(B_117, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_10, c_50, c_673])).
% 3.94/1.66  tff(c_42, plain, (![A_47]: (k3_xboole_0(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.94/1.66  tff(c_693, plain, (![B_117]: (k3_xboole_0(k5_relat_1(B_117, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_117, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_117, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_117, k1_xboole_0)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_681, c_42])).
% 3.94/1.66  tff(c_701, plain, (![B_118]: (k5_relat_1(B_118, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_118, k1_xboole_0)) | ~v1_relat_1(B_118))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_286, c_693])).
% 3.94/1.66  tff(c_705, plain, (![A_44]: (k5_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_38, c_701])).
% 3.94/1.66  tff(c_709, plain, (![A_119]: (k5_relat_1(A_119, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_705])).
% 3.94/1.66  tff(c_723, plain, (![A_43]: (k5_relat_1(k4_relat_1(A_43), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_43))), inference(resolution, [status(thm)], [c_36, c_709])).
% 3.94/1.66  tff(c_851, plain, (![B_136]: (k4_relat_1(k5_relat_1(k1_xboole_0, B_136))=k1_xboole_0 | ~v1_relat_1(B_136) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_811, c_723])).
% 3.94/1.66  tff(c_40, plain, (![A_46]: (k4_relat_1(k4_relat_1(A_46))=A_46 | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_878, plain, (![B_136]: (k5_relat_1(k1_xboole_0, B_136)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_136)) | ~v1_relat_1(B_136) | ~v1_relat_1(B_136))), inference(superposition, [status(thm), theory('equality')], [c_851, c_40])).
% 3.94/1.66  tff(c_1775, plain, (![B_161]: (k5_relat_1(k1_xboole_0, B_161)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_161)) | ~v1_relat_1(B_161) | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_634, c_878])).
% 3.94/1.66  tff(c_1785, plain, (![B_45]: (k5_relat_1(k1_xboole_0, B_45)=k1_xboole_0 | ~v1_relat_1(B_45) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_1775])).
% 3.94/1.66  tff(c_1791, plain, (![B_162]: (k5_relat_1(k1_xboole_0, B_162)=k1_xboole_0 | ~v1_relat_1(B_162))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1785])).
% 3.94/1.66  tff(c_1812, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_1791])).
% 3.94/1.66  tff(c_1823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_1812])).
% 3.94/1.66  tff(c_1824, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 3.94/1.66  tff(c_1878, plain, (![A_171, B_172]: (k5_xboole_0(A_171, k3_xboole_0(A_171, B_172))=k4_xboole_0(A_171, B_172))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.94/1.66  tff(c_1890, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1878])).
% 3.94/1.66  tff(c_1893, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1890])).
% 3.94/1.66  tff(c_1999, plain, (![C_186, A_187, B_188]: (k4_xboole_0(k2_zfmisc_1(C_186, A_187), k2_zfmisc_1(C_186, B_188))=k2_zfmisc_1(C_186, k4_xboole_0(A_187, B_188)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.66  tff(c_2006, plain, (![C_186, B_188]: (k2_zfmisc_1(C_186, k4_xboole_0(B_188, B_188))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1999, c_1893])).
% 3.94/1.66  tff(c_2015, plain, (![C_186]: (k2_zfmisc_1(C_186, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1893, c_2006])).
% 3.94/1.66  tff(c_2491, plain, (![B_223, A_224]: (k2_relat_1(k5_relat_1(B_223, A_224))=k2_relat_1(A_224) | ~r1_tarski(k1_relat_1(A_224), k2_relat_1(B_223)) | ~v1_relat_1(B_223) | ~v1_relat_1(A_224))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.94/1.66  tff(c_2494, plain, (![B_223]: (k2_relat_1(k5_relat_1(B_223, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_223)) | ~v1_relat_1(B_223) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2491])).
% 3.94/1.66  tff(c_2502, plain, (![B_225]: (k2_relat_1(k5_relat_1(B_225, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_225))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_10, c_50, c_2494])).
% 3.94/1.66  tff(c_2514, plain, (![B_225]: (k3_xboole_0(k5_relat_1(B_225, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_225, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_225, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_225, k1_xboole_0)) | ~v1_relat_1(B_225))), inference(superposition, [status(thm), theory('equality')], [c_2502, c_42])).
% 3.94/1.66  tff(c_2525, plain, (![B_226]: (k5_relat_1(B_226, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_226, k1_xboole_0)) | ~v1_relat_1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2015, c_2514])).
% 3.94/1.66  tff(c_2532, plain, (![A_44]: (k5_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_38, c_2525])).
% 3.94/1.66  tff(c_2536, plain, (![A_227]: (k5_relat_1(A_227, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_2532])).
% 3.94/1.66  tff(c_2548, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_2536])).
% 3.94/1.66  tff(c_2555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1824, c_2548])).
% 3.94/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.66  
% 3.94/1.66  Inference rules
% 3.94/1.66  ----------------------
% 3.94/1.66  #Ref     : 0
% 3.94/1.66  #Sup     : 602
% 3.94/1.66  #Fact    : 0
% 3.94/1.66  #Define  : 0
% 3.94/1.66  #Split   : 3
% 3.94/1.66  #Chain   : 0
% 3.94/1.66  #Close   : 0
% 3.94/1.66  
% 3.94/1.66  Ordering : KBO
% 3.94/1.66  
% 3.94/1.66  Simplification rules
% 3.94/1.66  ----------------------
% 3.94/1.66  #Subsume      : 17
% 3.94/1.66  #Demod        : 597
% 3.94/1.66  #Tautology    : 368
% 3.94/1.66  #SimpNegUnit  : 2
% 3.94/1.66  #BackRed      : 6
% 3.94/1.66  
% 3.94/1.66  #Partial instantiations: 0
% 3.94/1.66  #Strategies tried      : 1
% 3.94/1.66  
% 3.94/1.66  Timing (in seconds)
% 3.94/1.66  ----------------------
% 3.94/1.66  Preprocessing        : 0.32
% 3.94/1.66  Parsing              : 0.17
% 3.94/1.66  CNF conversion       : 0.02
% 3.94/1.66  Main loop            : 0.58
% 3.94/1.66  Inferencing          : 0.21
% 3.94/1.66  Reduction            : 0.20
% 3.94/1.66  Demodulation         : 0.15
% 3.94/1.66  BG Simplification    : 0.03
% 3.94/1.66  Subsumption          : 0.10
% 3.94/1.66  Abstraction          : 0.04
% 3.94/1.66  MUC search           : 0.00
% 3.94/1.66  Cooper               : 0.00
% 3.94/1.66  Total                : 0.94
% 3.94/1.66  Index Insertion      : 0.00
% 3.94/1.66  Index Deletion       : 0.00
% 3.94/1.66  Index Matching       : 0.00
% 3.94/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
