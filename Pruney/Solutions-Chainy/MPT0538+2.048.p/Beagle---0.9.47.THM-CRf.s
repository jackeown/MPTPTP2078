%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  75 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k8_relat_1(k2_relat_1(A),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_45,axiom,(
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

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_61,plain,(
    ! [A_47] :
      ( k8_relat_1(k2_relat_1(A_47),A_47) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_70,plain,
    ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_61])).

tff(c_73,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_22,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_2'(A_16),A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,k3_xboole_0(A_50,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_90,plain,(
    ! [A_6,C_52] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_52,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_83])).

tff(c_94,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_98,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_94])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_98])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_103,plain,(
    k8_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_176,plain,(
    ! [B_72,A_73,C_74] :
      ( k8_relat_1(B_72,k8_relat_1(A_73,C_74)) = k8_relat_1(A_73,C_74)
      | ~ r1_tarski(A_73,B_72)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_195,plain,(
    ! [B_72] :
      ( k8_relat_1(k1_xboole_0,k1_xboole_0) = k8_relat_1(B_72,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,B_72)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_176])).

tff(c_207,plain,(
    ! [B_72] : k8_relat_1(B_72,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_8,c_103,c_195])).

tff(c_32,plain,(
    k8_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.59  
% 2.43/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.43/1.59  
% 2.43/1.59  %Foreground sorts:
% 2.43/1.59  
% 2.43/1.59  
% 2.43/1.59  %Background operators:
% 2.43/1.59  
% 2.43/1.59  
% 2.43/1.59  %Foreground operators:
% 2.43/1.59  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.43/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.43/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.43/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.43/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.43/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.43/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.43/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.43/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.43/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.43/1.59  
% 2.43/1.61  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.43/1.61  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k8_relat_1(k2_relat_1(A), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_relat_1)).
% 2.43/1.61  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.43/1.61  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.43/1.61  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.43/1.61  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.43/1.61  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.43/1.61  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_relat_1)).
% 2.43/1.61  tff(f_77, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.43/1.61  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.43/1.61  tff(c_61, plain, (![A_47]: (k8_relat_1(k2_relat_1(A_47), A_47)=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.43/1.61  tff(c_70, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_61])).
% 2.43/1.61  tff(c_73, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_70])).
% 2.43/1.61  tff(c_22, plain, (![A_16]: (r2_hidden('#skF_2'(A_16), A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.61  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.43/1.61  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.61  tff(c_83, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, k3_xboole_0(A_50, B_51)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.43/1.61  tff(c_90, plain, (![A_6, C_52]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_52, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_83])).
% 2.43/1.61  tff(c_94, plain, (![C_53]: (~r2_hidden(C_53, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_90])).
% 2.43/1.61  tff(c_98, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_94])).
% 2.43/1.61  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_98])).
% 2.43/1.61  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_70])).
% 2.43/1.61  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.61  tff(c_103, plain, (k8_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_70])).
% 2.43/1.61  tff(c_176, plain, (![B_72, A_73, C_74]: (k8_relat_1(B_72, k8_relat_1(A_73, C_74))=k8_relat_1(A_73, C_74) | ~r1_tarski(A_73, B_72) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.43/1.61  tff(c_195, plain, (![B_72]: (k8_relat_1(k1_xboole_0, k1_xboole_0)=k8_relat_1(B_72, k1_xboole_0) | ~r1_tarski(k1_xboole_0, B_72) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_103, c_176])).
% 2.43/1.61  tff(c_207, plain, (![B_72]: (k8_relat_1(B_72, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_8, c_103, c_195])).
% 2.43/1.61  tff(c_32, plain, (k8_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.43/1.61  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_207, c_32])).
% 2.43/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.61  
% 2.43/1.61  Inference rules
% 2.43/1.61  ----------------------
% 2.43/1.61  #Ref     : 1
% 2.43/1.61  #Sup     : 39
% 2.43/1.61  #Fact    : 0
% 2.43/1.61  #Define  : 0
% 2.43/1.61  #Split   : 1
% 2.43/1.61  #Chain   : 0
% 2.43/1.61  #Close   : 0
% 2.43/1.61  
% 2.43/1.61  Ordering : KBO
% 2.43/1.61  
% 2.43/1.61  Simplification rules
% 2.43/1.61  ----------------------
% 2.43/1.61  #Subsume      : 0
% 2.43/1.61  #Demod        : 11
% 2.43/1.61  #Tautology    : 29
% 2.43/1.61  #SimpNegUnit  : 2
% 2.43/1.61  #BackRed      : 1
% 2.43/1.61  
% 2.43/1.61  #Partial instantiations: 0
% 2.43/1.61  #Strategies tried      : 1
% 2.43/1.61  
% 2.43/1.61  Timing (in seconds)
% 2.43/1.61  ----------------------
% 2.43/1.61  Preprocessing        : 0.50
% 2.43/1.61  Parsing              : 0.26
% 2.43/1.61  CNF conversion       : 0.03
% 2.43/1.62  Main loop            : 0.25
% 2.43/1.62  Inferencing          : 0.11
% 2.43/1.62  Reduction            : 0.07
% 2.43/1.62  Demodulation         : 0.05
% 2.43/1.62  BG Simplification    : 0.02
% 2.43/1.62  Subsumption          : 0.02
% 2.43/1.62  Abstraction          : 0.02
% 2.43/1.62  MUC search           : 0.00
% 2.43/1.62  Cooper               : 0.00
% 2.43/1.62  Total                : 0.80
% 2.43/1.62  Index Insertion      : 0.00
% 2.43/1.62  Index Deletion       : 0.00
% 2.43/1.62  Index Matching       : 0.00
% 2.43/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
