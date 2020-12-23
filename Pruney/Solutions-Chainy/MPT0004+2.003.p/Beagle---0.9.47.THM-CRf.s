%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 122 expanded)
%              Number of leaves         :   17 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 226 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ ( ~ r1_xboole_0(A,B)
            & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
        & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_49,axiom,(
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

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_35,plain,(
    k3_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31,c_30])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [C_12] :
      ( r1_xboole_0('#skF_2','#skF_3')
      | ~ r2_hidden(C_12,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_50,plain,(
    ! [A_21] : r1_xboole_0(A_21,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_22] : k3_xboole_0(A_22,k3_xboole_0('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_61,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_6])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_61])).

tff(c_71,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_75,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_2])).

tff(c_16,plain,(
    ! [C_12] :
      ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
      | ~ r2_hidden(C_12,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_99,plain,(
    ! [C_12] :
      ( r2_hidden('#skF_4',k1_xboole_0)
      | ~ r2_hidden(C_12,k3_xboole_0('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_16])).

tff(c_101,plain,(
    ! [C_29] : ~ r2_hidden(C_29,k3_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_112,plain,(
    ! [B_30] : r1_xboole_0(k3_xboole_0('#skF_5','#skF_6'),B_30) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_128,plain,(
    ! [B_32] : k3_xboole_0(k3_xboole_0('#skF_5','#skF_6'),B_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_134,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_134])).

tff(c_144,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_81,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,B_26)
      | ~ r2_hidden(C_27,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_145,plain,(
    ! [C_33,B_34,A_35] :
      ( ~ r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | k3_xboole_0(A_35,B_34) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_81])).

tff(c_155,plain,(
    ! [A_36] :
      ( ~ r2_hidden('#skF_4',A_36)
      | k3_xboole_0(A_36,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_144,c_145])).

tff(c_158,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_155])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_164,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_163,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_166,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_174,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_163,c_166])).

tff(c_20,plain,
    ( r2_hidden('#skF_4',k3_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_190,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_174,c_20])).

tff(c_192,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,B_46)
      | ~ r2_hidden(C_47,B_46)
      | ~ r2_hidden(C_47,A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_252,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | k3_xboole_0(A_55,B_54) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_266,plain,(
    ! [A_56] :
      ( ~ r2_hidden('#skF_4',A_56)
      | k3_xboole_0(A_56,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_190,c_252])).

tff(c_269,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_190,c_266])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.88/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.22  
% 2.03/1.23  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.03/1.23  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.03/1.23  tff(f_64, negated_conjecture, ~(![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.03/1.23  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.03/1.23  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.23  tff(c_31, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.23  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.23  tff(c_30, plain, (~r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_18])).
% 2.03/1.23  tff(c_35, plain, (k3_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_31, c_30])).
% 2.03/1.23  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.23  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.23  tff(c_14, plain, (![C_12]: (r1_xboole_0('#skF_2', '#skF_3') | ~r2_hidden(C_12, k3_xboole_0('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.23  tff(c_44, plain, (![C_20]: (~r2_hidden(C_20, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_14])).
% 2.03/1.23  tff(c_50, plain, (![A_21]: (r1_xboole_0(A_21, k3_xboole_0('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.03/1.23  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.23  tff(c_55, plain, (![A_22]: (k3_xboole_0(A_22, k3_xboole_0('#skF_5', '#skF_6'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.03/1.23  tff(c_61, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_55, c_6])).
% 2.03/1.23  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_61])).
% 2.03/1.23  tff(c_71, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_14])).
% 2.03/1.23  tff(c_75, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_2])).
% 2.03/1.23  tff(c_16, plain, (![C_12]: (r2_hidden('#skF_4', k3_xboole_0('#skF_2', '#skF_3')) | ~r2_hidden(C_12, k3_xboole_0('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.23  tff(c_99, plain, (![C_12]: (r2_hidden('#skF_4', k1_xboole_0) | ~r2_hidden(C_12, k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_16])).
% 2.03/1.23  tff(c_101, plain, (![C_29]: (~r2_hidden(C_29, k3_xboole_0('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_99])).
% 2.03/1.23  tff(c_112, plain, (![B_30]: (r1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'), B_30))), inference(resolution, [status(thm)], [c_12, c_101])).
% 2.03/1.23  tff(c_128, plain, (![B_32]: (k3_xboole_0(k3_xboole_0('#skF_5', '#skF_6'), B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.03/1.23  tff(c_134, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_128, c_6])).
% 2.03/1.23  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_134])).
% 2.03/1.23  tff(c_144, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_99])).
% 2.03/1.23  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.23  tff(c_81, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, B_26) | ~r2_hidden(C_27, A_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.23  tff(c_145, plain, (![C_33, B_34, A_35]: (~r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | k3_xboole_0(A_35, B_34)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_81])).
% 2.03/1.23  tff(c_155, plain, (![A_36]: (~r2_hidden('#skF_4', A_36) | k3_xboole_0(A_36, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_144, c_145])).
% 2.03/1.23  tff(c_158, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_155])).
% 2.03/1.23  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 2.03/1.23  tff(c_164, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 2.03/1.23  tff(c_163, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.03/1.23  tff(c_166, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.03/1.23  tff(c_174, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_163, c_166])).
% 2.03/1.23  tff(c_20, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.03/1.23  tff(c_190, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_164, c_174, c_20])).
% 2.03/1.23  tff(c_192, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, B_46) | ~r2_hidden(C_47, B_46) | ~r2_hidden(C_47, A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.03/1.23  tff(c_252, plain, (![C_53, B_54, A_55]: (~r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | k3_xboole_0(A_55, B_54)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_192])).
% 2.03/1.23  tff(c_266, plain, (![A_56]: (~r2_hidden('#skF_4', A_56) | k3_xboole_0(A_56, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_190, c_252])).
% 2.03/1.23  tff(c_269, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_190, c_266])).
% 2.03/1.23  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_269])).
% 2.03/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  Inference rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Ref     : 0
% 2.03/1.23  #Sup     : 56
% 2.03/1.23  #Fact    : 0
% 2.03/1.23  #Define  : 0
% 2.03/1.23  #Split   : 4
% 2.03/1.23  #Chain   : 0
% 2.03/1.23  #Close   : 0
% 2.03/1.23  
% 2.03/1.23  Ordering : KBO
% 2.03/1.23  
% 2.03/1.23  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 5
% 2.03/1.23  #Demod        : 11
% 2.03/1.23  #Tautology    : 18
% 2.03/1.23  #SimpNegUnit  : 2
% 2.03/1.23  #BackRed      : 0
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.03/1.23  Preprocessing        : 0.26
% 2.03/1.23  Parsing              : 0.15
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.19
% 2.03/1.23  Inferencing          : 0.08
% 2.03/1.23  Reduction            : 0.05
% 2.03/1.23  Demodulation         : 0.03
% 2.03/1.23  BG Simplification    : 0.01
% 2.03/1.23  Subsumption          : 0.04
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.24  MUC search           : 0.00
% 2.03/1.24  Cooper               : 0.00
% 2.03/1.24  Total                : 0.48
% 2.03/1.24  Index Insertion      : 0.00
% 2.03/1.24  Index Deletion       : 0.00
% 2.03/1.24  Index Matching       : 0.00
% 2.03/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
