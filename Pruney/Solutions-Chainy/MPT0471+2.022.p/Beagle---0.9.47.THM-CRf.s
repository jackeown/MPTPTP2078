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
% DateTime   : Thu Dec  3 09:59:23 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  78 expanded)
%              Number of equality atoms :   19 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_62,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_3'(A_31),A_31)
      | v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_113,plain,(
    ! [D_79,B_80,A_81] :
      ( ~ r2_hidden(D_79,B_80)
      | ~ r2_hidden(D_79,k4_xboole_0(A_81,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,(
    ! [D_82,A_83] :
      ( ~ r2_hidden(D_82,k1_xboole_0)
      | ~ r2_hidden(D_82,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_126,plain,(
    ! [A_83] :
      ( ~ r2_hidden('#skF_3'(k1_xboole_0),A_83)
      | v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_128,plain,(
    ! [A_84] : ~ r2_hidden('#skF_3'(k1_xboole_0),A_84) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_133,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_22,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_153,plain,(
    ! [A_94] :
      ( k2_xboole_0(k1_relat_1(A_94),k2_relat_1(A_94)) = k3_relat_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_162,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_153])).

tff(c_169,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_22,c_60,c_162])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_169])).

tff(c_172,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_182,plain,(
    ! [A_98] :
      ( k2_xboole_0(k1_relat_1(A_98),k2_relat_1(A_98)) = k3_relat_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_191,plain,
    ( k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_182])).

tff(c_198,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_60,c_22,c_191])).

tff(c_200,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:19:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  
% 1.99/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.23  %$ r2_hidden > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_2 > #skF_8 > #skF_9 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 1.99/1.23  
% 1.99/1.23  %Foreground sorts:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Background operators:
% 1.99/1.23  
% 1.99/1.23  
% 1.99/1.23  %Foreground operators:
% 1.99/1.23  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.99/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.23  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.99/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 1.99/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.99/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.23  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.99/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.99/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.99/1.23  
% 1.99/1.24  tff(f_79, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 1.99/1.24  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.99/1.24  tff(f_40, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.99/1.24  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.99/1.24  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.99/1.24  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.24  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.99/1.24  tff(c_62, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.99/1.24  tff(c_42, plain, (![A_31]: (r2_hidden('#skF_3'(A_31), A_31) | v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.99/1.24  tff(c_24, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.24  tff(c_113, plain, (![D_79, B_80, A_81]: (~r2_hidden(D_79, B_80) | ~r2_hidden(D_79, k4_xboole_0(A_81, B_80)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.99/1.24  tff(c_122, plain, (![D_82, A_83]: (~r2_hidden(D_82, k1_xboole_0) | ~r2_hidden(D_82, A_83))), inference(superposition, [status(thm), theory('equality')], [c_24, c_113])).
% 1.99/1.24  tff(c_126, plain, (![A_83]: (~r2_hidden('#skF_3'(k1_xboole_0), A_83) | v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_122])).
% 1.99/1.24  tff(c_128, plain, (![A_84]: (~r2_hidden('#skF_3'(k1_xboole_0), A_84))), inference(splitLeft, [status(thm)], [c_126])).
% 1.99/1.24  tff(c_133, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_128])).
% 1.99/1.24  tff(c_22, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.24  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.24  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.99/1.24  tff(c_153, plain, (![A_94]: (k2_xboole_0(k1_relat_1(A_94), k2_relat_1(A_94))=k3_relat_1(A_94) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.99/1.24  tff(c_162, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_153])).
% 1.99/1.24  tff(c_169, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_22, c_60, c_162])).
% 1.99/1.24  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_169])).
% 1.99/1.24  tff(c_172, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_126])).
% 1.99/1.24  tff(c_182, plain, (![A_98]: (k2_xboole_0(k1_relat_1(A_98), k2_relat_1(A_98))=k3_relat_1(A_98) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.99/1.24  tff(c_191, plain, (k2_xboole_0(k1_relat_1(k1_xboole_0), k1_xboole_0)=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_58, c_182])).
% 1.99/1.24  tff(c_198, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_60, c_22, c_191])).
% 1.99/1.24  tff(c_200, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_198])).
% 1.99/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  Inference rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Ref     : 0
% 1.99/1.24  #Sup     : 32
% 1.99/1.24  #Fact    : 0
% 1.99/1.24  #Define  : 0
% 1.99/1.24  #Split   : 1
% 1.99/1.24  #Chain   : 0
% 1.99/1.24  #Close   : 0
% 1.99/1.24  
% 1.99/1.24  Ordering : KBO
% 1.99/1.24  
% 1.99/1.24  Simplification rules
% 1.99/1.24  ----------------------
% 1.99/1.24  #Subsume      : 0
% 1.99/1.24  #Demod        : 6
% 1.99/1.24  #Tautology    : 22
% 1.99/1.24  #SimpNegUnit  : 2
% 1.99/1.24  #BackRed      : 0
% 1.99/1.24  
% 1.99/1.24  #Partial instantiations: 0
% 1.99/1.24  #Strategies tried      : 1
% 1.99/1.24  
% 1.99/1.24  Timing (in seconds)
% 1.99/1.24  ----------------------
% 1.99/1.24  Preprocessing        : 0.32
% 1.99/1.24  Parsing              : 0.16
% 1.99/1.24  CNF conversion       : 0.02
% 1.99/1.24  Main loop            : 0.14
% 1.99/1.24  Inferencing          : 0.04
% 1.99/1.24  Reduction            : 0.04
% 1.99/1.24  Demodulation         : 0.03
% 1.99/1.24  BG Simplification    : 0.02
% 1.99/1.24  Subsumption          : 0.03
% 1.99/1.24  Abstraction          : 0.01
% 1.99/1.24  MUC search           : 0.00
% 1.99/1.24  Cooper               : 0.00
% 1.99/1.24  Total                : 0.48
% 1.99/1.24  Index Insertion      : 0.00
% 1.99/1.24  Index Deletion       : 0.00
% 1.99/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
