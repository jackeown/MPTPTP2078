%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:39 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 (  67 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_10] :
      ( r1_tarski(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10)))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( ~ r1_xboole_0(A_29,B_30)
      | r1_xboole_0(k2_zfmisc_1(A_29,C_31),k2_zfmisc_1(B_30,D_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [A_45,C_46,B_47,D_48] :
      ( k4_xboole_0(k2_zfmisc_1(A_45,C_46),k2_zfmisc_1(B_47,D_48)) = k2_zfmisc_1(A_45,C_46)
      | ~ r1_xboole_0(A_45,B_47) ) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_57,D_56,B_53,A_55,C_54] :
      ( r1_xboole_0(A_57,k2_zfmisc_1(A_55,C_54))
      | ~ r1_tarski(A_57,k2_zfmisc_1(B_53,D_56))
      | ~ r1_xboole_0(A_55,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_147,plain,(
    ! [A_58,A_59,C_60] :
      ( r1_xboole_0(A_58,k2_zfmisc_1(A_59,C_60))
      | ~ r1_xboole_0(A_59,k1_relat_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_154,plain,(
    ! [C_60] :
      ( r1_xboole_0('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_1'),C_60))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_147])).

tff(c_166,plain,(
    ! [C_66] : r1_xboole_0('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_1'),C_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_154])).

tff(c_171,plain,(
    ! [C_67] : k4_xboole_0('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_1'),C_67)) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_166,c_2])).

tff(c_193,plain,(
    ! [A_70,C_71] :
      ( r1_xboole_0(A_70,'#skF_2')
      | ~ r1_tarski(A_70,k2_zfmisc_1(k1_relat_1('#skF_1'),C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_6])).

tff(c_197,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_193])).

tff(c_200,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_197])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.92/1.19  
% 1.92/1.19  %Foreground sorts:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Background operators:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Foreground operators:
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.19  
% 1.92/1.20  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 1.92/1.20  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.92/1.20  tff(f_39, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 1.92/1.20  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.92/1.20  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.92/1.20  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.20  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.20  tff(c_12, plain, (![A_10]: (r1_tarski(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10))) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.20  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.20  tff(c_16, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.20  tff(c_80, plain, (![A_29, B_30, C_31, D_32]: (~r1_xboole_0(A_29, B_30) | r1_xboole_0(k2_zfmisc_1(A_29, C_31), k2_zfmisc_1(B_30, D_32)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.20  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.20  tff(c_97, plain, (![A_45, C_46, B_47, D_48]: (k4_xboole_0(k2_zfmisc_1(A_45, C_46), k2_zfmisc_1(B_47, D_48))=k2_zfmisc_1(A_45, C_46) | ~r1_xboole_0(A_45, B_47))), inference(resolution, [status(thm)], [c_80, c_2])).
% 1.92/1.20  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.20  tff(c_143, plain, (![A_57, D_56, B_53, A_55, C_54]: (r1_xboole_0(A_57, k2_zfmisc_1(A_55, C_54)) | ~r1_tarski(A_57, k2_zfmisc_1(B_53, D_56)) | ~r1_xboole_0(A_55, B_53))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 1.92/1.20  tff(c_147, plain, (![A_58, A_59, C_60]: (r1_xboole_0(A_58, k2_zfmisc_1(A_59, C_60)) | ~r1_xboole_0(A_59, k1_relat_1(A_58)) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_12, c_143])).
% 1.92/1.20  tff(c_154, plain, (![C_60]: (r1_xboole_0('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_1'), C_60)) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_147])).
% 1.92/1.20  tff(c_166, plain, (![C_66]: (r1_xboole_0('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_1'), C_66)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_154])).
% 1.92/1.20  tff(c_171, plain, (![C_67]: (k4_xboole_0('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_1'), C_67))='#skF_2')), inference(resolution, [status(thm)], [c_166, c_2])).
% 1.92/1.20  tff(c_193, plain, (![A_70, C_71]: (r1_xboole_0(A_70, '#skF_2') | ~r1_tarski(A_70, k2_zfmisc_1(k1_relat_1('#skF_1'), C_71)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_6])).
% 1.92/1.20  tff(c_197, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_12, c_193])).
% 1.92/1.20  tff(c_200, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_197])).
% 1.92/1.20  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_200])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 48
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 0
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 2
% 1.92/1.20  #Demod        : 3
% 1.92/1.20  #Tautology    : 13
% 1.92/1.20  #SimpNegUnit  : 1
% 1.92/1.20  #BackRed      : 0
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.25
% 1.97/1.20  Parsing              : 0.14
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.20
% 1.97/1.20  Inferencing          : 0.09
% 1.97/1.20  Reduction            : 0.04
% 1.97/1.20  Demodulation         : 0.03
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.04
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.48
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
