%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:12 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  82 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( r2_hidden(k1_xboole_0,A)
       => k1_setfam_1(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_28,plain,(
    k1_setfam_1('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_setfam_1(B_14),A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden(A_31,B_32)
      | r2_hidden(A_31,C_33)
      | ~ r2_hidden(A_31,k5_xboole_0(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [A_34,A_35] :
      ( r2_hidden(A_34,A_35)
      | r2_hidden(A_34,A_35)
      | ~ r2_hidden(A_34,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_48])).

tff(c_73,plain,(
    ! [A_5,A_35] :
      ( r2_hidden('#skF_1'(A_5,k1_xboole_0),A_35)
      | r1_xboole_0(A_5,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_103,plain,(
    ! [A_43,C_44,B_45] :
      ( ~ r2_hidden(A_43,C_44)
      | ~ r2_hidden(A_43,B_45)
      | ~ r2_hidden(A_43,k5_xboole_0(B_45,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_135,plain,(
    ! [A_46,A_47] :
      ( ~ r2_hidden(A_46,A_47)
      | ~ r2_hidden(A_46,A_47)
      | ~ r2_hidden(A_46,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_103])).

tff(c_159,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_1'(A_48,B_49),B_49)
      | ~ r2_hidden('#skF_1'(A_48,B_49),k1_xboole_0)
      | r1_xboole_0(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_18,c_135])).

tff(c_183,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),k1_xboole_0)
      | r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_159])).

tff(c_214,plain,(
    ! [A_53] : r1_xboole_0(A_53,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_73,c_183])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( ~ r1_xboole_0(B_11,A_10)
      | ~ r1_tarski(B_11,A_10)
      | v1_xboole_0(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_242,plain,(
    ! [A_58] :
      ( ~ r1_tarski(A_58,k1_xboole_0)
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_214,c_22])).

tff(c_275,plain,(
    ! [B_63] :
      ( v1_xboole_0(k1_setfam_1(B_63))
      | ~ r2_hidden(k1_xboole_0,B_63) ) ),
    inference(resolution,[status(thm)],[c_26,c_242])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_280,plain,(
    ! [B_64] :
      ( k1_setfam_1(B_64) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_64) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_291,plain,(
    k1_setfam_1('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_280])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  
% 1.98/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k5_xboole_0 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.21  
% 1.98/1.21  %Foreground sorts:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Background operators:
% 1.98/1.21  
% 1.98/1.21  
% 1.98/1.21  %Foreground operators:
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.21  
% 1.98/1.22  tff(f_73, negated_conjecture, ~(![A]: (r2_hidden(k1_xboole_0, A) => (k1_setfam_1(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_setfam_1)).
% 1.98/1.22  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 1.98/1.22  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.98/1.22  tff(f_64, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.98/1.22  tff(f_36, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 1.98/1.22  tff(f_62, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.98/1.22  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.98/1.22  tff(c_28, plain, (k1_setfam_1('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.22  tff(c_30, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.22  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k1_setfam_1(B_14), A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.22  tff(c_18, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.98/1.22  tff(c_24, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.98/1.22  tff(c_48, plain, (![A_31, B_32, C_33]: (r2_hidden(A_31, B_32) | r2_hidden(A_31, C_33) | ~r2_hidden(A_31, k5_xboole_0(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.22  tff(c_66, plain, (![A_34, A_35]: (r2_hidden(A_34, A_35) | r2_hidden(A_34, A_35) | ~r2_hidden(A_34, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_48])).
% 1.98/1.22  tff(c_73, plain, (![A_5, A_35]: (r2_hidden('#skF_1'(A_5, k1_xboole_0), A_35) | r1_xboole_0(A_5, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_66])).
% 1.98/1.22  tff(c_103, plain, (![A_43, C_44, B_45]: (~r2_hidden(A_43, C_44) | ~r2_hidden(A_43, B_45) | ~r2_hidden(A_43, k5_xboole_0(B_45, C_44)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.98/1.22  tff(c_135, plain, (![A_46, A_47]: (~r2_hidden(A_46, A_47) | ~r2_hidden(A_46, A_47) | ~r2_hidden(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_103])).
% 1.98/1.22  tff(c_159, plain, (![A_48, B_49]: (~r2_hidden('#skF_1'(A_48, B_49), B_49) | ~r2_hidden('#skF_1'(A_48, B_49), k1_xboole_0) | r1_xboole_0(A_48, B_49))), inference(resolution, [status(thm)], [c_18, c_135])).
% 1.98/1.22  tff(c_183, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), k1_xboole_0) | r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_18, c_159])).
% 1.98/1.22  tff(c_214, plain, (![A_53]: (r1_xboole_0(A_53, k1_xboole_0))), inference(resolution, [status(thm)], [c_73, c_183])).
% 1.98/1.22  tff(c_22, plain, (![B_11, A_10]: (~r1_xboole_0(B_11, A_10) | ~r1_tarski(B_11, A_10) | v1_xboole_0(B_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.98/1.22  tff(c_242, plain, (![A_58]: (~r1_tarski(A_58, k1_xboole_0) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_214, c_22])).
% 1.98/1.22  tff(c_275, plain, (![B_63]: (v1_xboole_0(k1_setfam_1(B_63)) | ~r2_hidden(k1_xboole_0, B_63))), inference(resolution, [status(thm)], [c_26, c_242])).
% 1.98/1.22  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.98/1.22  tff(c_280, plain, (![B_64]: (k1_setfam_1(B_64)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_64))), inference(resolution, [status(thm)], [c_275, c_2])).
% 1.98/1.22  tff(c_291, plain, (k1_setfam_1('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_280])).
% 1.98/1.22  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_291])).
% 1.98/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.22  
% 1.98/1.22  Inference rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Ref     : 0
% 1.98/1.22  #Sup     : 59
% 1.98/1.22  #Fact    : 0
% 1.98/1.22  #Define  : 0
% 1.98/1.22  #Split   : 1
% 1.98/1.22  #Chain   : 0
% 1.98/1.22  #Close   : 0
% 1.98/1.22  
% 1.98/1.22  Ordering : KBO
% 1.98/1.22  
% 1.98/1.22  Simplification rules
% 1.98/1.22  ----------------------
% 1.98/1.22  #Subsume      : 10
% 1.98/1.22  #Demod        : 10
% 1.98/1.22  #Tautology    : 17
% 1.98/1.22  #SimpNegUnit  : 1
% 1.98/1.22  #BackRed      : 0
% 1.98/1.22  
% 1.98/1.22  #Partial instantiations: 0
% 1.98/1.22  #Strategies tried      : 1
% 1.98/1.22  
% 1.98/1.22  Timing (in seconds)
% 1.98/1.22  ----------------------
% 1.98/1.23  Preprocessing        : 0.25
% 1.98/1.23  Parsing              : 0.14
% 1.98/1.23  CNF conversion       : 0.02
% 1.98/1.23  Main loop            : 0.21
% 1.98/1.23  Inferencing          : 0.08
% 1.98/1.23  Reduction            : 0.05
% 1.98/1.23  Demodulation         : 0.03
% 1.98/1.23  BG Simplification    : 0.01
% 1.98/1.23  Subsumption          : 0.05
% 1.98/1.23  Abstraction          : 0.01
% 1.98/1.23  MUC search           : 0.00
% 1.98/1.23  Cooper               : 0.00
% 1.98/1.23  Total                : 0.48
% 1.98/1.23  Index Insertion      : 0.00
% 1.98/1.23  Index Deletion       : 0.00
% 1.98/1.23  Index Matching       : 0.00
% 1.98/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
