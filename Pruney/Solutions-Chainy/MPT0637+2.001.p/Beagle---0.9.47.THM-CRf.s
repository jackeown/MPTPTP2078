%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:24 EST 2020

% Result     : Theorem 8.86s
% Output     : CNFRefutation 8.86s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  67 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_142,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_93,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_160,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_169,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_178,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_363,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,A_80) = k3_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_386,plain,(
    ! [B_79,A_80] : r1_tarski(k3_xboole_0(B_79,A_80),A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_14])).

tff(c_70,plain,(
    ! [A_42] : k1_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_44,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ! [A_42] : k2_relat_1(k6_relat_1(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_1636,plain,(
    ! [B_157,A_158] :
      ( k5_relat_1(B_157,k6_relat_1(A_158)) = B_157
      | ~ r1_tarski(k2_relat_1(B_157),A_158)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1647,plain,(
    ! [A_42,A_158] :
      ( k5_relat_1(k6_relat_1(A_42),k6_relat_1(A_158)) = k6_relat_1(A_42)
      | ~ r1_tarski(A_42,A_158)
      | ~ v1_relat_1(k6_relat_1(A_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1636])).

tff(c_5491,plain,(
    ! [A_260,A_261] :
      ( k5_relat_1(k6_relat_1(A_260),k6_relat_1(A_261)) = k6_relat_1(A_260)
      | ~ r1_tarski(A_260,A_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1647])).

tff(c_86,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_5506,plain,(
    ! [A_261,A_260] :
      ( k7_relat_1(k6_relat_1(A_261),A_260) = k6_relat_1(A_260)
      | ~ v1_relat_1(k6_relat_1(A_261))
      | ~ r1_tarski(A_260,A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5491,c_86])).

tff(c_18944,plain,(
    ! [A_431,A_432] :
      ( k7_relat_1(k6_relat_1(A_431),A_432) = k6_relat_1(A_432)
      | ~ r1_tarski(A_432,A_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5506])).

tff(c_2075,plain,(
    ! [B_172,A_173] :
      ( k7_relat_1(B_172,k3_xboole_0(k1_relat_1(B_172),A_173)) = k7_relat_1(B_172,A_173)
      | ~ v1_relat_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2105,plain,(
    ! [B_172,A_1] :
      ( k7_relat_1(B_172,k3_xboole_0(A_1,k1_relat_1(B_172))) = k7_relat_1(B_172,A_1)
      | ~ v1_relat_1(B_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2075])).

tff(c_18972,plain,(
    ! [A_1,A_431] :
      ( k6_relat_1(k3_xboole_0(A_1,k1_relat_1(k6_relat_1(A_431)))) = k7_relat_1(k6_relat_1(A_431),A_1)
      | ~ v1_relat_1(k6_relat_1(A_431))
      | ~ r1_tarski(k3_xboole_0(A_1,k1_relat_1(k6_relat_1(A_431))),A_431) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18944,c_2105])).

tff(c_19084,plain,(
    ! [A_431,A_1] : k7_relat_1(k6_relat_1(A_431),A_1) = k6_relat_1(k3_xboole_0(A_1,A_431)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_70,c_44,c_70,c_18972])).

tff(c_1056,plain,(
    ! [A_128,B_129] :
      ( k5_relat_1(k6_relat_1(A_128),B_129) = k7_relat_1(B_129,A_128)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_92,plain,(
    k5_relat_1(k6_relat_1('#skF_5'),k6_relat_1('#skF_4')) != k6_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1089,plain,
    ( k7_relat_1(k6_relat_1('#skF_4'),'#skF_5') != k6_relat_1(k3_xboole_0('#skF_4','#skF_5'))
    | ~ v1_relat_1(k6_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_92])).

tff(c_1124,plain,(
    k7_relat_1(k6_relat_1('#skF_4'),'#skF_5') != k6_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1089])).

tff(c_19128,plain,(
    k6_relat_1(k3_xboole_0('#skF_5','#skF_4')) != k6_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19084,c_1124])).

tff(c_19133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_19128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.86/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/3.47  
% 8.86/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/3.47  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.86/3.47  
% 8.86/3.47  %Foreground sorts:
% 8.86/3.47  
% 8.86/3.47  
% 8.86/3.47  %Background operators:
% 8.86/3.47  
% 8.86/3.47  
% 8.86/3.47  %Foreground operators:
% 8.86/3.47  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 8.86/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.86/3.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.86/3.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.86/3.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.86/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.86/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.86/3.47  tff('#skF_5', type, '#skF_5': $i).
% 8.86/3.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.86/3.47  tff('#skF_2', type, '#skF_2': $i).
% 8.86/3.47  tff('#skF_3', type, '#skF_3': $i).
% 8.86/3.47  tff('#skF_1', type, '#skF_1': $i).
% 8.86/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.86/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.86/3.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.86/3.47  tff('#skF_4', type, '#skF_4': $i).
% 8.86/3.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.86/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.86/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.86/3.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.86/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.86/3.47  
% 8.86/3.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.86/3.48  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 8.86/3.48  tff(f_142, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.86/3.48  tff(f_93, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 8.86/3.48  tff(f_160, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 8.86/3.48  tff(f_169, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 8.86/3.48  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 8.86/3.48  tff(f_178, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.86/3.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.86/3.48  tff(c_363, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k3_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.86/3.48  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.86/3.48  tff(c_386, plain, (![B_79, A_80]: (r1_tarski(k3_xboole_0(B_79, A_80), A_80))), inference(superposition, [status(thm), theory('equality')], [c_363, c_14])).
% 8.86/3.48  tff(c_70, plain, (![A_42]: (k1_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/3.48  tff(c_44, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 8.86/3.48  tff(c_72, plain, (![A_42]: (k2_relat_1(k6_relat_1(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_142])).
% 8.86/3.48  tff(c_1636, plain, (![B_157, A_158]: (k5_relat_1(B_157, k6_relat_1(A_158))=B_157 | ~r1_tarski(k2_relat_1(B_157), A_158) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.86/3.48  tff(c_1647, plain, (![A_42, A_158]: (k5_relat_1(k6_relat_1(A_42), k6_relat_1(A_158))=k6_relat_1(A_42) | ~r1_tarski(A_42, A_158) | ~v1_relat_1(k6_relat_1(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1636])).
% 8.86/3.48  tff(c_5491, plain, (![A_260, A_261]: (k5_relat_1(k6_relat_1(A_260), k6_relat_1(A_261))=k6_relat_1(A_260) | ~r1_tarski(A_260, A_261))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1647])).
% 8.86/3.48  tff(c_86, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.86/3.48  tff(c_5506, plain, (![A_261, A_260]: (k7_relat_1(k6_relat_1(A_261), A_260)=k6_relat_1(A_260) | ~v1_relat_1(k6_relat_1(A_261)) | ~r1_tarski(A_260, A_261))), inference(superposition, [status(thm), theory('equality')], [c_5491, c_86])).
% 8.86/3.48  tff(c_18944, plain, (![A_431, A_432]: (k7_relat_1(k6_relat_1(A_431), A_432)=k6_relat_1(A_432) | ~r1_tarski(A_432, A_431))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5506])).
% 8.86/3.48  tff(c_2075, plain, (![B_172, A_173]: (k7_relat_1(B_172, k3_xboole_0(k1_relat_1(B_172), A_173))=k7_relat_1(B_172, A_173) | ~v1_relat_1(B_172))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.86/3.48  tff(c_2105, plain, (![B_172, A_1]: (k7_relat_1(B_172, k3_xboole_0(A_1, k1_relat_1(B_172)))=k7_relat_1(B_172, A_1) | ~v1_relat_1(B_172))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2075])).
% 8.86/3.48  tff(c_18972, plain, (![A_1, A_431]: (k6_relat_1(k3_xboole_0(A_1, k1_relat_1(k6_relat_1(A_431))))=k7_relat_1(k6_relat_1(A_431), A_1) | ~v1_relat_1(k6_relat_1(A_431)) | ~r1_tarski(k3_xboole_0(A_1, k1_relat_1(k6_relat_1(A_431))), A_431))), inference(superposition, [status(thm), theory('equality')], [c_18944, c_2105])).
% 8.86/3.48  tff(c_19084, plain, (![A_431, A_1]: (k7_relat_1(k6_relat_1(A_431), A_1)=k6_relat_1(k3_xboole_0(A_1, A_431)))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_70, c_44, c_70, c_18972])).
% 8.86/3.48  tff(c_1056, plain, (![A_128, B_129]: (k5_relat_1(k6_relat_1(A_128), B_129)=k7_relat_1(B_129, A_128) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.86/3.48  tff(c_92, plain, (k5_relat_1(k6_relat_1('#skF_5'), k6_relat_1('#skF_4'))!=k6_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.86/3.48  tff(c_1089, plain, (k7_relat_1(k6_relat_1('#skF_4'), '#skF_5')!=k6_relat_1(k3_xboole_0('#skF_4', '#skF_5')) | ~v1_relat_1(k6_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1056, c_92])).
% 8.86/3.48  tff(c_1124, plain, (k7_relat_1(k6_relat_1('#skF_4'), '#skF_5')!=k6_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1089])).
% 8.86/3.48  tff(c_19128, plain, (k6_relat_1(k3_xboole_0('#skF_5', '#skF_4'))!=k6_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_19084, c_1124])).
% 8.86/3.48  tff(c_19133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_19128])).
% 8.86/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.86/3.48  
% 8.86/3.48  Inference rules
% 8.86/3.48  ----------------------
% 8.86/3.48  #Ref     : 0
% 8.86/3.48  #Sup     : 4610
% 8.86/3.48  #Fact    : 0
% 8.86/3.48  #Define  : 0
% 8.86/3.48  #Split   : 5
% 8.86/3.48  #Chain   : 0
% 8.86/3.48  #Close   : 0
% 8.86/3.48  
% 8.86/3.48  Ordering : KBO
% 8.86/3.48  
% 8.86/3.48  Simplification rules
% 8.86/3.48  ----------------------
% 8.86/3.48  #Subsume      : 962
% 8.86/3.48  #Demod        : 4415
% 8.86/3.48  #Tautology    : 2170
% 8.86/3.48  #SimpNegUnit  : 10
% 8.86/3.48  #BackRed      : 29
% 8.86/3.48  
% 8.86/3.48  #Partial instantiations: 0
% 8.86/3.48  #Strategies tried      : 1
% 8.86/3.48  
% 8.86/3.48  Timing (in seconds)
% 8.86/3.48  ----------------------
% 9.07/3.48  Preprocessing        : 0.35
% 9.07/3.48  Parsing              : 0.20
% 9.07/3.48  CNF conversion       : 0.02
% 9.07/3.48  Main loop            : 2.33
% 9.07/3.48  Inferencing          : 0.52
% 9.07/3.48  Reduction            : 1.02
% 9.07/3.48  Demodulation         : 0.82
% 9.07/3.48  BG Simplification    : 0.07
% 9.07/3.48  Subsumption          : 0.59
% 9.07/3.48  Abstraction          : 0.09
% 9.07/3.48  MUC search           : 0.00
% 9.07/3.48  Cooper               : 0.00
% 9.07/3.48  Total                : 2.70
% 9.07/3.48  Index Insertion      : 0.00
% 9.07/3.48  Index Deletion       : 0.00
% 9.07/3.48  Index Matching       : 0.00
% 9.07/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
