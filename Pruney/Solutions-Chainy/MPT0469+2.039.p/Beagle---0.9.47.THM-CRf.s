%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   55 (  73 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  90 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_32,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [C_74,A_75] :
      ( r2_hidden(k4_tarski(C_74,'#skF_9'(A_75,k1_relat_1(A_75),C_74)),A_75)
      | ~ r2_hidden(C_74,k1_relat_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,k3_xboole_0(A_57,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_8,C_59] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_59,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_60,plain,(
    ! [C_59] : ~ r2_hidden(C_59,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_113,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_98,c_60])).

tff(c_125,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_125])).

tff(c_138,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_146,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r1_xboole_0(A_81,B_82)
      | ~ r2_hidden(C_83,k3_xboole_0(A_81,B_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_157,plain,(
    ! [A_8,C_83] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_83,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_161,plain,(
    ! [C_83] : ~ r2_hidden(C_83,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_16,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_3'(A_10),A_10)
      | v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [C_84] : ~ r2_hidden(C_84,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_157])).

tff(c_173,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_162])).

tff(c_139,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_197,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_10'(A_94,B_95),k1_relat_1(B_95))
      | ~ r2_hidden(A_94,k2_relat_1(B_95))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_200,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_10'(A_94,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_94,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_197])).

tff(c_202,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_10'(A_94,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_94,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_200])).

tff(c_204,plain,(
    ! [A_96] : ~ r2_hidden(A_96,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_202])).

tff(c_208,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_204])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.20  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 1.89/1.20  
% 1.89/1.20  %Foreground sorts:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Background operators:
% 1.89/1.20  
% 1.89/1.20  
% 1.89/1.20  %Foreground operators:
% 1.89/1.20  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.89/1.20  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.89/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.89/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.20  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 1.89/1.20  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 1.89/1.20  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.89/1.20  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.89/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.20  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.89/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.20  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.89/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.89/1.20  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.89/1.20  
% 1.89/1.21  tff(f_82, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.89/1.21  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.89/1.21  tff(f_69, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.89/1.21  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.21  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.89/1.21  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.89/1.21  tff(f_61, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.89/1.21  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 1.89/1.21  tff(c_32, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.89/1.21  tff(c_42, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.89/1.21  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.21  tff(c_98, plain, (![C_74, A_75]: (r2_hidden(k4_tarski(C_74, '#skF_9'(A_75, k1_relat_1(A_75), C_74)), A_75) | ~r2_hidden(C_74, k1_relat_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.89/1.21  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.21  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.21  tff(c_45, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.21  tff(c_56, plain, (![A_8, C_59]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_59, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_45])).
% 1.89/1.21  tff(c_60, plain, (![C_59]: (~r2_hidden(C_59, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 1.89/1.21  tff(c_113, plain, (![C_76]: (~r2_hidden(C_76, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_98, c_60])).
% 1.89/1.21  tff(c_125, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_113])).
% 1.89/1.21  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_125])).
% 1.89/1.21  tff(c_138, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.89/1.21  tff(c_146, plain, (![A_81, B_82, C_83]: (~r1_xboole_0(A_81, B_82) | ~r2_hidden(C_83, k3_xboole_0(A_81, B_82)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.21  tff(c_157, plain, (![A_8, C_83]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_146])).
% 1.89/1.21  tff(c_161, plain, (![C_83]: (~r2_hidden(C_83, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_157])).
% 1.89/1.21  tff(c_16, plain, (![A_10]: (r2_hidden('#skF_3'(A_10), A_10) | v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.89/1.21  tff(c_162, plain, (![C_84]: (~r2_hidden(C_84, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_157])).
% 1.89/1.21  tff(c_173, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_162])).
% 1.89/1.21  tff(c_139, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.89/1.21  tff(c_197, plain, (![A_94, B_95]: (r2_hidden('#skF_10'(A_94, B_95), k1_relat_1(B_95)) | ~r2_hidden(A_94, k2_relat_1(B_95)) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_78])).
% 1.89/1.21  tff(c_200, plain, (![A_94]: (r2_hidden('#skF_10'(A_94, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_94, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_139, c_197])).
% 1.89/1.21  tff(c_202, plain, (![A_94]: (r2_hidden('#skF_10'(A_94, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_94, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_200])).
% 1.89/1.21  tff(c_204, plain, (![A_96]: (~r2_hidden(A_96, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_161, c_202])).
% 1.89/1.21  tff(c_208, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_204])).
% 1.89/1.21  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_208])).
% 1.89/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  Inference rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Ref     : 0
% 1.89/1.21  #Sup     : 32
% 1.89/1.21  #Fact    : 0
% 1.89/1.21  #Define  : 0
% 1.89/1.21  #Split   : 1
% 1.89/1.21  #Chain   : 0
% 1.89/1.21  #Close   : 0
% 1.89/1.21  
% 1.89/1.21  Ordering : KBO
% 1.89/1.21  
% 1.89/1.21  Simplification rules
% 1.89/1.21  ----------------------
% 1.89/1.21  #Subsume      : 0
% 1.89/1.21  #Demod        : 12
% 1.89/1.21  #Tautology    : 15
% 1.89/1.21  #SimpNegUnit  : 5
% 1.89/1.21  #BackRed      : 0
% 1.89/1.21  
% 1.89/1.21  #Partial instantiations: 0
% 1.89/1.21  #Strategies tried      : 1
% 1.89/1.21  
% 1.89/1.21  Timing (in seconds)
% 1.89/1.21  ----------------------
% 1.89/1.21  Preprocessing        : 0.30
% 1.89/1.21  Parsing              : 0.16
% 1.89/1.21  CNF conversion       : 0.03
% 1.89/1.21  Main loop            : 0.15
% 1.89/1.21  Inferencing          : 0.06
% 1.89/1.21  Reduction            : 0.04
% 1.89/1.21  Demodulation         : 0.03
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.02
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.48
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
