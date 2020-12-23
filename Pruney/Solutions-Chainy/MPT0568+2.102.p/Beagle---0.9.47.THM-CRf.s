%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   56 ( 112 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_80,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_68,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_34,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_34])).

tff(c_219,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(k4_tarski(A_61,'#skF_4'(A_61,B_62,C_63)),C_63)
      | ~ r2_hidden(A_61,k10_relat_1(C_63,B_62))
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_4'(A_17,B_18,C_19),B_18)
      | ~ r2_hidden(A_17,k10_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_108,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_4'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k10_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_41,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,B_33)
      | ~ r2_hidden(C_34,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [C_34,A_8] :
      ( ~ r2_hidden(C_34,k1_xboole_0)
      | ~ r2_hidden(C_34,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_41])).

tff(c_119,plain,(
    ! [A_50,C_51,A_52] :
      ( ~ r2_hidden('#skF_4'(A_50,k1_xboole_0,C_51),A_52)
      | ~ r2_hidden(A_50,k10_relat_1(C_51,k1_xboole_0))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_108,c_44])).

tff(c_131,plain,(
    ! [A_56,C_57] :
      ( ~ r2_hidden(A_56,k10_relat_1(C_57,k1_xboole_0))
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_157,plain,(
    ! [C_58] :
      ( ~ v1_relat_1(C_58)
      | k10_relat_1(C_58,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_131])).

tff(c_164,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_157])).

tff(c_124,plain,(
    ! [A_17,C_19] :
      ( ~ r2_hidden(A_17,k10_relat_1(C_19,k1_xboole_0))
      | ~ v1_relat_1(C_19) ) ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_169,plain,(
    ! [A_17] :
      ( ~ r2_hidden(A_17,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_124])).

tff(c_173,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_169])).

tff(c_223,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden(A_61,k10_relat_1(k1_xboole_0,B_62))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_219,c_173])).

tff(c_237,plain,(
    ! [A_64,B_65] : ~ r2_hidden(A_64,k10_relat_1(k1_xboole_0,B_65)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_223])).

tff(c_269,plain,(
    ! [B_65] : k10_relat_1(k1_xboole_0,B_65) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  
% 2.22/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 2.22/1.38  
% 2.22/1.38  %Foreground sorts:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Background operators:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Foreground operators:
% 2.22/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.22/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.22/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.22/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.38  
% 2.22/1.40  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.22/1.40  tff(f_80, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.22/1.40  tff(f_68, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.22/1.40  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.22/1.40  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.22/1.40  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.22/1.40  tff(f_83, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.22/1.40  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.40  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.40  tff(c_34, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.40  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_34])).
% 2.22/1.40  tff(c_219, plain, (![A_61, B_62, C_63]: (r2_hidden(k4_tarski(A_61, '#skF_4'(A_61, B_62, C_63)), C_63) | ~r2_hidden(A_61, k10_relat_1(C_63, B_62)) | ~v1_relat_1(C_63))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.40  tff(c_20, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_4'(A_17, B_18, C_19), B_18) | ~r2_hidden(A_17, k10_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.40  tff(c_108, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_4'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k10_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.40  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.22/1.40  tff(c_41, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, B_33) | ~r2_hidden(C_34, A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.40  tff(c_44, plain, (![C_34, A_8]: (~r2_hidden(C_34, k1_xboole_0) | ~r2_hidden(C_34, A_8))), inference(resolution, [status(thm)], [c_10, c_41])).
% 2.22/1.40  tff(c_119, plain, (![A_50, C_51, A_52]: (~r2_hidden('#skF_4'(A_50, k1_xboole_0, C_51), A_52) | ~r2_hidden(A_50, k10_relat_1(C_51, k1_xboole_0)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_108, c_44])).
% 2.22/1.40  tff(c_131, plain, (![A_56, C_57]: (~r2_hidden(A_56, k10_relat_1(C_57, k1_xboole_0)) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_20, c_119])).
% 2.22/1.40  tff(c_157, plain, (![C_58]: (~v1_relat_1(C_58) | k10_relat_1(C_58, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_131])).
% 2.22/1.40  tff(c_164, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_157])).
% 2.22/1.40  tff(c_124, plain, (![A_17, C_19]: (~r2_hidden(A_17, k10_relat_1(C_19, k1_xboole_0)) | ~v1_relat_1(C_19))), inference(resolution, [status(thm)], [c_20, c_119])).
% 2.22/1.40  tff(c_169, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_164, c_124])).
% 2.22/1.40  tff(c_173, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_169])).
% 2.22/1.40  tff(c_223, plain, (![A_61, B_62]: (~r2_hidden(A_61, k10_relat_1(k1_xboole_0, B_62)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_219, c_173])).
% 2.22/1.40  tff(c_237, plain, (![A_64, B_65]: (~r2_hidden(A_64, k10_relat_1(k1_xboole_0, B_65)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_223])).
% 2.22/1.40  tff(c_269, plain, (![B_65]: (k10_relat_1(k1_xboole_0, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_237])).
% 2.22/1.40  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.22/1.40  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_28])).
% 2.22/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.40  
% 2.22/1.40  Inference rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Ref     : 0
% 2.22/1.40  #Sup     : 49
% 2.22/1.40  #Fact    : 0
% 2.22/1.40  #Define  : 0
% 2.22/1.40  #Split   : 0
% 2.22/1.40  #Chain   : 0
% 2.22/1.40  #Close   : 0
% 2.22/1.40  
% 2.22/1.40  Ordering : KBO
% 2.22/1.40  
% 2.22/1.40  Simplification rules
% 2.22/1.40  ----------------------
% 2.22/1.40  #Subsume      : 12
% 2.22/1.40  #Demod        : 12
% 2.22/1.40  #Tautology    : 15
% 2.22/1.40  #SimpNegUnit  : 0
% 2.22/1.40  #BackRed      : 2
% 2.22/1.40  
% 2.22/1.40  #Partial instantiations: 0
% 2.22/1.40  #Strategies tried      : 1
% 2.22/1.40  
% 2.22/1.40  Timing (in seconds)
% 2.22/1.40  ----------------------
% 2.22/1.40  Preprocessing        : 0.37
% 2.22/1.40  Parsing              : 0.20
% 2.22/1.40  CNF conversion       : 0.03
% 2.22/1.40  Main loop            : 0.21
% 2.22/1.40  Inferencing          : 0.09
% 2.22/1.40  Reduction            : 0.05
% 2.22/1.40  Demodulation         : 0.04
% 2.22/1.40  BG Simplification    : 0.01
% 2.22/1.40  Subsumption          : 0.04
% 2.22/1.40  Abstraction          : 0.01
% 2.22/1.40  MUC search           : 0.00
% 2.22/1.40  Cooper               : 0.00
% 2.22/1.40  Total                : 0.61
% 2.22/1.40  Index Insertion      : 0.00
% 2.22/1.40  Index Deletion       : 0.00
% 2.22/1.40  Index Matching       : 0.00
% 2.22/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
