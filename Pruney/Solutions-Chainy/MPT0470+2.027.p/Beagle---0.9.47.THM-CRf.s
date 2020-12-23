%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 112 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  121 ( 194 expanded)
%              Number of equality atoms :   34 (  53 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,(
    ! [A_25,B_26] :
      ( v1_xboole_0(k2_zfmisc_1(A_25,B_26))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_130,plain,(
    ! [A_35,B_36] :
      ( k2_zfmisc_1(A_35,B_36) = k1_xboole_0
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_139,plain,(
    ! [B_36] : k2_zfmisc_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_509,plain,(
    ! [A_58,B_59] :
      ( k1_relat_1(k5_relat_1(A_58,B_59)) = k1_relat_1(A_58)
      | ~ r1_tarski(k2_relat_1(A_58),k1_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_515,plain,(
    ! [B_59] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_59)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_509])).

tff(c_520,plain,(
    ! [B_60] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_60)) = k1_xboole_0
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_30,c_515])).

tff(c_22,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_529,plain,(
    ! [B_60] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_60),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_60))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_520,c_22])).

tff(c_566,plain,(
    ! [B_62] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_62),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_529])).

tff(c_102,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_576,plain,(
    ! [B_63] :
      ( k5_relat_1(k1_xboole_0,B_63) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(resolution,[status(thm)],[c_566,c_111])).

tff(c_580,plain,(
    ! [B_11] :
      ( k5_relat_1(k1_xboole_0,B_11) = k1_xboole_0
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_576])).

tff(c_622,plain,(
    ! [B_65] :
      ( k5_relat_1(k1_xboole_0,B_65) = k1_xboole_0
      | ~ v1_relat_1(B_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_580])).

tff(c_637,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_622])).

tff(c_645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_637])).

tff(c_646,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_661,plain,(
    ! [A_68,B_69] :
      ( v1_xboole_0(k2_zfmisc_1(A_68,B_69))
      | ~ v1_xboole_0(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_724,plain,(
    ! [A_78,B_79] :
      ( k2_zfmisc_1(A_78,B_79) = k1_xboole_0
      | ~ v1_xboole_0(B_79) ) ),
    inference(resolution,[status(thm)],[c_661,c_4])).

tff(c_733,plain,(
    ! [A_78] : k2_zfmisc_1(A_78,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_724])).

tff(c_1089,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_98,B_99)),k2_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1097,plain,(
    ! [A_98] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_98,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1089])).

tff(c_1103,plain,(
    ! [A_100] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_100,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1097])).

tff(c_701,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_710,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_701])).

tff(c_1113,plain,(
    ! [A_101] :
      ( k2_relat_1(k5_relat_1(A_101,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_101) ) ),
    inference(resolution,[status(thm)],[c_1103,c_710])).

tff(c_1128,plain,(
    ! [A_101] :
      ( r1_tarski(k5_relat_1(A_101,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_101,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_101,k1_xboole_0))
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1113,c_22])).

tff(c_1444,plain,(
    ! [A_115] :
      ( r1_tarski(k5_relat_1(A_115,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_115,k1_xboole_0))
      | ~ v1_relat_1(A_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_1128])).

tff(c_1459,plain,(
    ! [A_116] :
      ( k5_relat_1(A_116,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_116,k1_xboole_0))
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_1444,c_710])).

tff(c_1466,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_1459])).

tff(c_1472,plain,(
    ! [A_117] :
      ( k5_relat_1(A_117,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1466])).

tff(c_1487,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1472])).

tff(c_1496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_1487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.41  
% 2.85/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.41  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.85/1.41  
% 2.85/1.41  %Foreground sorts:
% 2.85/1.41  
% 2.85/1.41  
% 2.85/1.41  %Background operators:
% 2.85/1.41  
% 2.85/1.41  
% 2.85/1.41  %Foreground operators:
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.85/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.85/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.85/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.85/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.85/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.85/1.41  
% 2.85/1.42  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.85/1.42  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.85/1.42  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.85/1.42  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.85/1.42  tff(f_46, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 2.85/1.42  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.85/1.42  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.85/1.42  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.85/1.42  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.85/1.42  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.85/1.42  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.85/1.42  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.85/1.42  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.85/1.42  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.42  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.85/1.42  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.85/1.42  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.85/1.42  tff(c_52, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.85/1.42  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.85/1.42  tff(c_20, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.85/1.42  tff(c_67, plain, (![A_25, B_26]: (v1_xboole_0(k2_zfmisc_1(A_25, B_26)) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.85/1.42  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.85/1.42  tff(c_130, plain, (![A_35, B_36]: (k2_zfmisc_1(A_35, B_36)=k1_xboole_0 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_67, c_4])).
% 2.85/1.42  tff(c_139, plain, (![B_36]: (k2_zfmisc_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_130])).
% 2.85/1.42  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.85/1.42  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.42  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.85/1.42  tff(c_509, plain, (![A_58, B_59]: (k1_relat_1(k5_relat_1(A_58, B_59))=k1_relat_1(A_58) | ~r1_tarski(k2_relat_1(A_58), k1_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.85/1.42  tff(c_515, plain, (![B_59]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_59))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_509])).
% 2.85/1.42  tff(c_520, plain, (![B_60]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_60))=k1_xboole_0 | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_30, c_515])).
% 2.85/1.42  tff(c_22, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.42  tff(c_529, plain, (![B_60]: (r1_tarski(k5_relat_1(k1_xboole_0, B_60), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_60)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_60)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_520, c_22])).
% 2.85/1.42  tff(c_566, plain, (![B_62]: (r1_tarski(k5_relat_1(k1_xboole_0, B_62), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_62)) | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_529])).
% 2.85/1.42  tff(c_102, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.85/1.42  tff(c_111, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_102])).
% 2.85/1.42  tff(c_576, plain, (![B_63]: (k5_relat_1(k1_xboole_0, B_63)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_63)) | ~v1_relat_1(B_63))), inference(resolution, [status(thm)], [c_566, c_111])).
% 2.85/1.42  tff(c_580, plain, (![B_11]: (k5_relat_1(k1_xboole_0, B_11)=k1_xboole_0 | ~v1_relat_1(B_11) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_576])).
% 2.85/1.42  tff(c_622, plain, (![B_65]: (k5_relat_1(k1_xboole_0, B_65)=k1_xboole_0 | ~v1_relat_1(B_65))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_580])).
% 2.85/1.42  tff(c_637, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_622])).
% 2.85/1.42  tff(c_645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_637])).
% 2.85/1.42  tff(c_646, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.85/1.42  tff(c_661, plain, (![A_68, B_69]: (v1_xboole_0(k2_zfmisc_1(A_68, B_69)) | ~v1_xboole_0(B_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.85/1.42  tff(c_724, plain, (![A_78, B_79]: (k2_zfmisc_1(A_78, B_79)=k1_xboole_0 | ~v1_xboole_0(B_79))), inference(resolution, [status(thm)], [c_661, c_4])).
% 2.85/1.42  tff(c_733, plain, (![A_78]: (k2_zfmisc_1(A_78, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_724])).
% 2.85/1.42  tff(c_1089, plain, (![A_98, B_99]: (r1_tarski(k2_relat_1(k5_relat_1(A_98, B_99)), k2_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.85/1.42  tff(c_1097, plain, (![A_98]: (r1_tarski(k2_relat_1(k5_relat_1(A_98, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_98))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1089])).
% 2.85/1.42  tff(c_1103, plain, (![A_100]: (r1_tarski(k2_relat_1(k5_relat_1(A_100, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1097])).
% 2.85/1.42  tff(c_701, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.85/1.42  tff(c_710, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_701])).
% 2.85/1.42  tff(c_1113, plain, (![A_101]: (k2_relat_1(k5_relat_1(A_101, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_101))), inference(resolution, [status(thm)], [c_1103, c_710])).
% 2.85/1.42  tff(c_1128, plain, (![A_101]: (r1_tarski(k5_relat_1(A_101, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_101, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_101, k1_xboole_0)) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_1113, c_22])).
% 2.85/1.42  tff(c_1444, plain, (![A_115]: (r1_tarski(k5_relat_1(A_115, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_115, k1_xboole_0)) | ~v1_relat_1(A_115))), inference(demodulation, [status(thm), theory('equality')], [c_733, c_1128])).
% 2.85/1.42  tff(c_1459, plain, (![A_116]: (k5_relat_1(A_116, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_116, k1_xboole_0)) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_1444, c_710])).
% 2.85/1.42  tff(c_1466, plain, (![A_10]: (k5_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_20, c_1459])).
% 2.85/1.42  tff(c_1472, plain, (![A_117]: (k5_relat_1(A_117, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1466])).
% 2.85/1.42  tff(c_1487, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1472])).
% 2.85/1.42  tff(c_1496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_1487])).
% 2.85/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.43  
% 2.85/1.43  Inference rules
% 2.85/1.43  ----------------------
% 2.85/1.43  #Ref     : 0
% 2.85/1.43  #Sup     : 337
% 2.85/1.43  #Fact    : 0
% 2.85/1.43  #Define  : 0
% 2.85/1.43  #Split   : 1
% 2.85/1.43  #Chain   : 0
% 2.85/1.43  #Close   : 0
% 2.85/1.43  
% 2.85/1.43  Ordering : KBO
% 2.85/1.43  
% 2.85/1.43  Simplification rules
% 2.85/1.43  ----------------------
% 2.85/1.43  #Subsume      : 6
% 2.85/1.43  #Demod        : 268
% 2.85/1.43  #Tautology    : 262
% 2.85/1.43  #SimpNegUnit  : 2
% 2.85/1.43  #BackRed      : 0
% 2.85/1.43  
% 2.85/1.43  #Partial instantiations: 0
% 2.85/1.43  #Strategies tried      : 1
% 2.85/1.43  
% 2.85/1.43  Timing (in seconds)
% 2.85/1.43  ----------------------
% 2.85/1.43  Preprocessing        : 0.28
% 2.85/1.43  Parsing              : 0.15
% 2.85/1.43  CNF conversion       : 0.02
% 2.85/1.43  Main loop            : 0.39
% 2.85/1.43  Inferencing          : 0.15
% 2.85/1.43  Reduction            : 0.11
% 2.85/1.43  Demodulation         : 0.08
% 2.85/1.43  BG Simplification    : 0.02
% 2.85/1.43  Subsumption          : 0.08
% 2.85/1.43  Abstraction          : 0.02
% 2.85/1.43  MUC search           : 0.00
% 2.85/1.43  Cooper               : 0.00
% 2.85/1.43  Total                : 0.70
% 2.85/1.43  Index Insertion      : 0.00
% 2.85/1.43  Index Deletion       : 0.00
% 2.85/1.43  Index Matching       : 0.00
% 2.85/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
