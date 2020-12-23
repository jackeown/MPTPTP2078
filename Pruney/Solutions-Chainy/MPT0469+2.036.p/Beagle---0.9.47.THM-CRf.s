%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:56 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 107 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_38,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_181,plain,(
    ! [C_91,A_92] :
      ( r2_hidden(k4_tarski(C_91,'#skF_9'(A_92,k1_relat_1(A_92),C_91)),A_92)
      | ~ r2_hidden(C_91,k1_relat_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [A_10,C_69] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_90,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_86])).

tff(c_205,plain,(
    ! [C_93] : ~ r2_hidden(C_93,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_181,c_90])).

tff(c_227,plain,(
    v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(B_61)
      | B_61 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_67,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ v1_xboole_0(A_62) ) ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_232,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_227,c_67])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_232])).

tff(c_243,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_260,plain,(
    ! [A_100,B_101,C_102] :
      ( ~ r1_xboole_0(A_100,B_101)
      | ~ r2_hidden(C_102,k3_xboole_0(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_271,plain,(
    ! [A_10,C_102] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_102,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_260])).

tff(c_275,plain,(
    ! [C_102] : ~ r2_hidden(C_102,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_271])).

tff(c_53,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_3'(A_59),A_59)
      | v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(A_60)
      | v1_relat_1(A_60) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_244,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_350,plain,(
    ! [A_120,B_121] :
      ( r2_hidden('#skF_10'(A_120,B_121),k1_relat_1(B_121))
      | ~ r2_hidden(A_120,k2_relat_1(B_121))
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_356,plain,(
    ! [A_120] :
      ( r2_hidden('#skF_10'(A_120,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_120,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_350])).

tff(c_359,plain,(
    ! [A_120] :
      ( r2_hidden('#skF_10'(A_120,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_120,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_356])).

tff(c_361,plain,(
    ! [A_122] : ~ r2_hidden(A_122,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_359])).

tff(c_371,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_361])).

tff(c_249,plain,(
    ! [B_94,A_95] :
      ( ~ v1_xboole_0(B_94)
      | B_94 = A_95
      | ~ v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_252,plain,(
    ! [A_95] :
      ( k1_xboole_0 = A_95
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_249])).

tff(c_406,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_371,c_252])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n009.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 09:58:26 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.19  
% 2.04/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.19  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5 > #skF_4
% 2.04/1.19  
% 2.04/1.19  %Foreground sorts:
% 2.04/1.19  
% 2.04/1.19  
% 2.04/1.19  %Background operators:
% 2.04/1.19  
% 2.04/1.19  
% 2.04/1.19  %Foreground operators:
% 2.04/1.19  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.04/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.04/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.04/1.19  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 2.04/1.19  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.04/1.19  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.04/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.04/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.04/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.19  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.04/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.19  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.04/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.19  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.04/1.19  
% 2.12/1.21  tff(f_89, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.21  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.12/1.21  tff(f_76, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.12/1.21  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.21  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.21  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.21  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.21  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.12/1.21  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.12/1.21  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 2.12/1.21  tff(c_38, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.12/1.21  tff(c_63, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.12/1.21  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.21  tff(c_181, plain, (![C_91, A_92]: (r2_hidden(k4_tarski(C_91, '#skF_9'(A_92, k1_relat_1(A_92), C_91)), A_92) | ~r2_hidden(C_91, k1_relat_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.21  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.21  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.12/1.21  tff(c_75, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.21  tff(c_86, plain, (![A_10, C_69]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_75])).
% 2.12/1.21  tff(c_90, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_86])).
% 2.12/1.21  tff(c_205, plain, (![C_93]: (~r2_hidden(C_93, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_181, c_90])).
% 2.12/1.21  tff(c_227, plain, (v1_xboole_0(k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_205])).
% 2.12/1.21  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.21  tff(c_64, plain, (![B_61, A_62]: (~v1_xboole_0(B_61) | B_61=A_62 | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.21  tff(c_67, plain, (![A_62]: (k1_xboole_0=A_62 | ~v1_xboole_0(A_62))), inference(resolution, [status(thm)], [c_6, c_64])).
% 2.12/1.21  tff(c_232, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_227, c_67])).
% 2.12/1.21  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_232])).
% 2.12/1.21  tff(c_243, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.12/1.21  tff(c_260, plain, (![A_100, B_101, C_102]: (~r1_xboole_0(A_100, B_101) | ~r2_hidden(C_102, k3_xboole_0(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.21  tff(c_271, plain, (![A_10, C_102]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_102, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_260])).
% 2.12/1.21  tff(c_275, plain, (![C_102]: (~r2_hidden(C_102, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_271])).
% 2.12/1.21  tff(c_53, plain, (![A_59]: (r2_hidden('#skF_3'(A_59), A_59) | v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.12/1.21  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.21  tff(c_58, plain, (![A_60]: (~v1_xboole_0(A_60) | v1_relat_1(A_60))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.12/1.21  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_58])).
% 2.12/1.21  tff(c_244, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.12/1.21  tff(c_350, plain, (![A_120, B_121]: (r2_hidden('#skF_10'(A_120, B_121), k1_relat_1(B_121)) | ~r2_hidden(A_120, k2_relat_1(B_121)) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.21  tff(c_356, plain, (![A_120]: (r2_hidden('#skF_10'(A_120, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_120, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_244, c_350])).
% 2.12/1.21  tff(c_359, plain, (![A_120]: (r2_hidden('#skF_10'(A_120, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_120, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_356])).
% 2.12/1.21  tff(c_361, plain, (![A_122]: (~r2_hidden(A_122, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_275, c_359])).
% 2.12/1.21  tff(c_371, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_361])).
% 2.12/1.21  tff(c_249, plain, (![B_94, A_95]: (~v1_xboole_0(B_94) | B_94=A_95 | ~v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.21  tff(c_252, plain, (![A_95]: (k1_xboole_0=A_95 | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_6, c_249])).
% 2.12/1.21  tff(c_406, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_371, c_252])).
% 2.12/1.21  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_406])).
% 2.12/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.21  
% 2.12/1.21  Inference rules
% 2.12/1.21  ----------------------
% 2.12/1.21  #Ref     : 0
% 2.12/1.21  #Sup     : 77
% 2.12/1.21  #Fact    : 0
% 2.12/1.21  #Define  : 0
% 2.12/1.21  #Split   : 1
% 2.12/1.21  #Chain   : 0
% 2.12/1.21  #Close   : 0
% 2.12/1.21  
% 2.12/1.21  Ordering : KBO
% 2.12/1.21  
% 2.12/1.21  Simplification rules
% 2.12/1.21  ----------------------
% 2.12/1.21  #Subsume      : 6
% 2.12/1.21  #Demod        : 26
% 2.12/1.21  #Tautology    : 27
% 2.12/1.21  #SimpNegUnit  : 6
% 2.12/1.21  #BackRed      : 0
% 2.12/1.21  
% 2.12/1.21  #Partial instantiations: 0
% 2.12/1.21  #Strategies tried      : 1
% 2.12/1.21  
% 2.12/1.21  Timing (in seconds)
% 2.12/1.21  ----------------------
% 2.12/1.21  Preprocessing        : 0.36
% 2.12/1.21  Parsing              : 0.19
% 2.12/1.21  CNF conversion       : 0.03
% 2.12/1.21  Main loop            : 0.23
% 2.12/1.21  Inferencing          : 0.10
% 2.12/1.21  Reduction            : 0.06
% 2.12/1.21  Demodulation         : 0.04
% 2.12/1.21  BG Simplification    : 0.01
% 2.12/1.21  Subsumption          : 0.04
% 2.12/1.21  Abstraction          : 0.01
% 2.12/1.21  MUC search           : 0.00
% 2.12/1.21  Cooper               : 0.00
% 2.12/1.21  Total                : 0.63
% 2.12/1.21  Index Insertion      : 0.00
% 2.12/1.21  Index Deletion       : 0.00
% 2.12/1.21  Index Matching       : 0.00
% 2.12/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
