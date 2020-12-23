%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  83 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    ! [A_41] :
      ( k9_relat_1(A_41,k1_relat_1(A_41)) = k2_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_84,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_75])).

tff(c_87,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_84])).

tff(c_88,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_20,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_6,C_48] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_178,plain,(
    ! [C_49] : ~ r2_hidden(C_49,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_174])).

tff(c_182,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_178])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_182])).

tff(c_188,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_187,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_193,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_203,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_12])).

tff(c_423,plain,(
    ! [B_70,A_71] :
      ( k9_relat_1(B_70,k3_xboole_0(k1_relat_1(B_70),A_71)) = k9_relat_1(B_70,A_71)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_440,plain,(
    ! [A_71] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_71)) = k9_relat_1(k1_xboole_0,A_71)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_423])).

tff(c_446,plain,(
    ! [A_71] : k9_relat_1(k1_xboole_0,A_71) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_187,c_203,c_440])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.32  
% 2.03/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.32  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.03/1.32  
% 2.03/1.32  %Foreground sorts:
% 2.03/1.32  
% 2.03/1.32  
% 2.03/1.32  %Background operators:
% 2.03/1.32  
% 2.03/1.32  
% 2.03/1.32  %Foreground operators:
% 2.03/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.03/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.03/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.03/1.32  
% 2.03/1.33  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.03/1.33  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.03/1.33  tff(f_59, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.03/1.33  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.03/1.33  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.03/1.33  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.03/1.33  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.03/1.33  tff(f_47, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.03/1.33  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 2.03/1.33  tff(f_73, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.03/1.33  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.03/1.33  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.03/1.33  tff(c_75, plain, (![A_41]: (k9_relat_1(A_41, k1_relat_1(A_41))=k2_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.33  tff(c_84, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_75])).
% 2.03/1.33  tff(c_87, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_84])).
% 2.03/1.33  tff(c_88, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_87])).
% 2.03/1.33  tff(c_20, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.03/1.33  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.33  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.03/1.33  tff(c_164, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.33  tff(c_174, plain, (![A_6, C_48]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_164])).
% 2.03/1.33  tff(c_178, plain, (![C_49]: (~r2_hidden(C_49, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_174])).
% 2.03/1.33  tff(c_182, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_178])).
% 2.03/1.33  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_182])).
% 2.03/1.33  tff(c_188, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_87])).
% 2.03/1.33  tff(c_187, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_87])).
% 2.03/1.33  tff(c_193, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.03/1.33  tff(c_12, plain, (![A_10]: (k4_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.33  tff(c_203, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_12])).
% 2.03/1.33  tff(c_423, plain, (![B_70, A_71]: (k9_relat_1(B_70, k3_xboole_0(k1_relat_1(B_70), A_71))=k9_relat_1(B_70, A_71) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.33  tff(c_440, plain, (![A_71]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_71))=k9_relat_1(k1_xboole_0, A_71) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_423])).
% 2.03/1.33  tff(c_446, plain, (![A_71]: (k9_relat_1(k1_xboole_0, A_71)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_187, c_203, c_440])).
% 2.03/1.33  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.03/1.33  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_446, c_30])).
% 2.03/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.33  
% 2.03/1.33  Inference rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Ref     : 0
% 2.03/1.33  #Sup     : 96
% 2.03/1.33  #Fact    : 0
% 2.03/1.33  #Define  : 0
% 2.03/1.33  #Split   : 1
% 2.03/1.33  #Chain   : 0
% 2.03/1.33  #Close   : 0
% 2.03/1.33  
% 2.03/1.33  Ordering : KBO
% 2.03/1.33  
% 2.03/1.33  Simplification rules
% 2.03/1.33  ----------------------
% 2.03/1.33  #Subsume      : 3
% 2.03/1.33  #Demod        : 38
% 2.03/1.33  #Tautology    : 68
% 2.03/1.33  #SimpNegUnit  : 3
% 2.03/1.33  #BackRed      : 1
% 2.03/1.33  
% 2.03/1.33  #Partial instantiations: 0
% 2.03/1.33  #Strategies tried      : 1
% 2.03/1.33  
% 2.03/1.33  Timing (in seconds)
% 2.03/1.33  ----------------------
% 2.03/1.33  Preprocessing        : 0.30
% 2.03/1.33  Parsing              : 0.18
% 2.03/1.33  CNF conversion       : 0.02
% 2.03/1.33  Main loop            : 0.22
% 2.03/1.33  Inferencing          : 0.09
% 2.03/1.33  Reduction            : 0.07
% 2.03/1.33  Demodulation         : 0.05
% 2.03/1.33  BG Simplification    : 0.01
% 2.03/1.33  Subsumption          : 0.03
% 2.03/1.33  Abstraction          : 0.01
% 2.03/1.33  MUC search           : 0.00
% 2.03/1.33  Cooper               : 0.00
% 2.03/1.33  Total                : 0.55
% 2.03/1.33  Index Insertion      : 0.00
% 2.03/1.33  Index Deletion       : 0.00
% 2.03/1.33  Index Matching       : 0.00
% 2.03/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
