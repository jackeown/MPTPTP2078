%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  66 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_52,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k7_relat_1(B_45,A_46),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_46] :
      ( k7_relat_1(k1_xboole_0,A_46) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_67,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_22,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_84,plain,(
    ! [A_6,C_53] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_77])).

tff(c_88,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_92,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_96,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_92])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_97,plain,(
    ! [A_46] : k7_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_149,plain,(
    ! [B_64,A_65] :
      ( k2_relat_1(k7_relat_1(B_64,A_65)) = k9_relat_1(B_64,A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_158,plain,(
    ! [A_46] :
      ( k9_relat_1(k1_xboole_0,A_46) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_149])).

tff(c_162,plain,(
    ! [A_46] : k9_relat_1(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_26,c_158])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:00:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  
% 1.98/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.29  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.98/1.29  
% 1.98/1.29  %Foreground sorts:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Background operators:
% 1.98/1.29  
% 1.98/1.29  
% 1.98/1.29  %Foreground operators:
% 1.98/1.29  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.98/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.98/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.98/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.98/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.98/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.98/1.29  tff('#skF_5', type, '#skF_5': $i).
% 1.98/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.98/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.98/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.98/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.98/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.98/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.98/1.29  
% 1.98/1.30  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.98/1.30  tff(f_45, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.98/1.30  tff(f_63, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.98/1.30  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.98/1.30  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.98/1.30  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.98/1.30  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.98/1.30  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.98/1.30  tff(f_77, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.98/1.30  tff(c_52, plain, (![B_45, A_46]: (r1_tarski(k7_relat_1(B_45, A_46), B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.98/1.30  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.30  tff(c_57, plain, (![A_46]: (k7_relat_1(k1_xboole_0, A_46)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_8])).
% 1.98/1.30  tff(c_67, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_57])).
% 1.98/1.30  tff(c_22, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.98/1.30  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.30  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.98/1.30  tff(c_77, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.30  tff(c_84, plain, (![A_6, C_53]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_77])).
% 1.98/1.30  tff(c_88, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 1.98/1.30  tff(c_92, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_88])).
% 1.98/1.30  tff(c_96, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_92])).
% 1.98/1.30  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_57])).
% 1.98/1.30  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.98/1.30  tff(c_97, plain, (![A_46]: (k7_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(splitRight, [status(thm)], [c_57])).
% 1.98/1.30  tff(c_149, plain, (![B_64, A_65]: (k2_relat_1(k7_relat_1(B_64, A_65))=k9_relat_1(B_64, A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.98/1.30  tff(c_158, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_97, c_149])).
% 1.98/1.30  tff(c_162, plain, (![A_46]: (k9_relat_1(k1_xboole_0, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_98, c_26, c_158])).
% 1.98/1.30  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.98/1.30  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_32])).
% 1.98/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.30  
% 1.98/1.30  Inference rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Ref     : 0
% 1.98/1.30  #Sup     : 27
% 1.98/1.30  #Fact    : 0
% 1.98/1.30  #Define  : 0
% 1.98/1.30  #Split   : 1
% 1.98/1.30  #Chain   : 0
% 1.98/1.30  #Close   : 0
% 1.98/1.30  
% 1.98/1.30  Ordering : KBO
% 1.98/1.30  
% 1.98/1.30  Simplification rules
% 1.98/1.30  ----------------------
% 1.98/1.30  #Subsume      : 0
% 1.98/1.30  #Demod        : 9
% 1.98/1.30  #Tautology    : 19
% 1.98/1.30  #SimpNegUnit  : 1
% 1.98/1.30  #BackRed      : 1
% 1.98/1.30  
% 1.98/1.30  #Partial instantiations: 0
% 1.98/1.30  #Strategies tried      : 1
% 1.98/1.30  
% 1.98/1.30  Timing (in seconds)
% 1.98/1.30  ----------------------
% 1.98/1.31  Preprocessing        : 0.32
% 1.98/1.31  Parsing              : 0.18
% 1.98/1.31  CNF conversion       : 0.02
% 1.98/1.31  Main loop            : 0.13
% 1.98/1.31  Inferencing          : 0.05
% 1.98/1.31  Reduction            : 0.04
% 1.98/1.31  Demodulation         : 0.03
% 1.98/1.31  BG Simplification    : 0.01
% 1.98/1.31  Subsumption          : 0.01
% 1.98/1.31  Abstraction          : 0.01
% 1.98/1.31  MUC search           : 0.00
% 1.98/1.31  Cooper               : 0.00
% 1.98/1.31  Total                : 0.48
% 1.98/1.31  Index Insertion      : 0.00
% 1.98/1.31  Index Deletion       : 0.00
% 1.98/1.31  Index Matching       : 0.00
% 1.98/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
