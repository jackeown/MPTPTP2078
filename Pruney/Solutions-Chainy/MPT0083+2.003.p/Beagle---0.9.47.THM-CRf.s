%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:01 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :   69 (  99 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :   76 ( 117 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_26,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_536,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_551,plain,(
    ! [A_14,C_62] :
      ( ~ r1_xboole_0(A_14,k1_xboole_0)
      | ~ r2_hidden(C_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_536])).

tff(c_559,plain,(
    ! [C_62] : ~ r2_hidden(C_62,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_551])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_331,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_346,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_331])).

tff(c_349,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_346])).

tff(c_20,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_334,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,k4_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_22])).

tff(c_1983,plain,(
    ! [A_112,B_113] : k3_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k4_xboole_0(A_112,B_113) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_334])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2052,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = A_112 ),
    inference(superposition,[status(thm),theory(equality)],[c_1983,c_14])).

tff(c_379,plain,(
    ! [A_56] : k4_xboole_0(A_56,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_346])).

tff(c_384,plain,(
    ! [A_56] : k4_xboole_0(A_56,k1_xboole_0) = k3_xboole_0(A_56,A_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_22])).

tff(c_396,plain,(
    ! [A_56] : k3_xboole_0(A_56,A_56) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_850,plain,(
    ! [A_83,B_84,C_85] : k2_xboole_0(k4_xboole_0(A_83,B_84),k3_xboole_0(A_83,C_85)) = k4_xboole_0(A_83,k4_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4425,plain,(
    ! [A_170,C_171,B_172] : k2_xboole_0(k3_xboole_0(A_170,C_171),k4_xboole_0(A_170,B_172)) = k4_xboole_0(A_170,k4_xboole_0(B_172,C_171)) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_2])).

tff(c_4554,plain,(
    ! [A_56,B_172] : k4_xboole_0(A_56,k4_xboole_0(B_172,A_56)) = k2_xboole_0(A_56,k4_xboole_0(A_56,B_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_4425])).

tff(c_4633,plain,(
    ! [A_173,B_174] : k4_xboole_0(A_173,k4_xboole_0(B_174,A_173)) = A_173 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2052,c_4554])).

tff(c_4804,plain,(
    ! [A_173,B_174] : k3_xboole_0(A_173,k4_xboole_0(B_174,A_173)) = k4_xboole_0(A_173,A_173) ),
    inference(superposition,[status(thm),theory(equality)],[c_4633,c_22])).

tff(c_5110,plain,(
    ! [A_177,B_178] : k3_xboole_0(A_177,k4_xboole_0(B_178,A_177)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_4804])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),k3_xboole_0(A_7,B_8))
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5206,plain,(
    ! [A_177,B_178] :
      ( r2_hidden('#skF_1'(A_177,k4_xboole_0(B_178,A_177)),k1_xboole_0)
      | r1_xboole_0(A_177,k4_xboole_0(B_178,A_177)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5110,c_10])).

tff(c_5330,plain,(
    ! [A_177,B_178] : r1_xboole_0(A_177,k4_xboole_0(B_178,A_177)) ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_5206])).

tff(c_30,plain,(
    ! [A_24,C_26,B_25] :
      ( r1_xboole_0(A_24,C_26)
      | ~ r1_xboole_0(A_24,k2_xboole_0(B_25,C_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6752,plain,(
    ! [A_202,A_203,C_204,B_205] :
      ( r1_xboole_0(A_202,k3_xboole_0(A_203,C_204))
      | ~ r1_xboole_0(A_202,k4_xboole_0(A_203,k4_xboole_0(B_205,C_204))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_30])).

tff(c_7222,plain,(
    ! [B_211,C_212,B_213] : r1_xboole_0(k4_xboole_0(B_211,C_212),k3_xboole_0(B_213,C_212)) ),
    inference(resolution,[status(thm)],[c_5330,c_6752])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7367,plain,(
    ! [B_213,C_212,B_211] : r1_xboole_0(k3_xboole_0(B_213,C_212),k4_xboole_0(B_211,C_212)) ),
    inference(resolution,[status(thm)],[c_7222,c_8])).

tff(c_36,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_197,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_xboole_0(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_206,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_197])).

tff(c_350,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = k4_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_365,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_350])).

tff(c_376,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_365])).

tff(c_23269,plain,(
    ! [A_423,A_424] :
      ( r1_xboole_0(A_423,k3_xboole_0(A_424,'#skF_3'))
      | ~ r1_xboole_0(A_423,k4_xboole_0(A_424,'#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_6752])).

tff(c_23461,plain,(
    ! [B_213,B_211] : r1_xboole_0(k3_xboole_0(B_213,'#skF_2'),k3_xboole_0(B_211,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_7367,c_23269])).

tff(c_34,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23461,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.94  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.94  
% 9.55/3.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.94  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.55/3.94  
% 9.55/3.94  %Foreground sorts:
% 9.55/3.94  
% 9.55/3.94  
% 9.55/3.94  %Background operators:
% 9.55/3.94  
% 9.55/3.94  
% 9.55/3.94  %Foreground operators:
% 9.55/3.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.55/3.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.55/3.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.55/3.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.55/3.94  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.55/3.94  tff('#skF_2', type, '#skF_2': $i).
% 9.55/3.94  tff('#skF_3', type, '#skF_3': $i).
% 9.55/3.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.55/3.94  tff('#skF_4', type, '#skF_4': $i).
% 9.55/3.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.55/3.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.55/3.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.55/3.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.55/3.94  
% 9.55/3.96  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.55/3.96  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.55/3.96  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.55/3.96  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.55/3.96  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.55/3.96  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.55/3.96  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.55/3.96  tff(f_61, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 9.55/3.96  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 9.55/3.96  tff(f_79, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 9.55/3.96  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.55/3.96  tff(f_84, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 9.55/3.96  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.55/3.96  tff(c_26, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.55/3.96  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.55/3.96  tff(c_536, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.55/3.96  tff(c_551, plain, (![A_14, C_62]: (~r1_xboole_0(A_14, k1_xboole_0) | ~r2_hidden(C_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_536])).
% 9.55/3.96  tff(c_559, plain, (![C_62]: (~r2_hidden(C_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_551])).
% 9.55/3.96  tff(c_18, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.55/3.96  tff(c_331, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.55/3.96  tff(c_346, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_331])).
% 9.55/3.96  tff(c_349, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_346])).
% 9.55/3.96  tff(c_20, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.55/3.96  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.55/3.96  tff(c_334, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_331, c_22])).
% 9.55/3.96  tff(c_1983, plain, (![A_112, B_113]: (k3_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k4_xboole_0(A_112, B_113))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_334])).
% 9.55/3.96  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k3_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.55/3.96  tff(c_2052, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(A_112, B_113))=A_112)), inference(superposition, [status(thm), theory('equality')], [c_1983, c_14])).
% 9.55/3.96  tff(c_379, plain, (![A_56]: (k4_xboole_0(A_56, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_346])).
% 9.55/3.96  tff(c_384, plain, (![A_56]: (k4_xboole_0(A_56, k1_xboole_0)=k3_xboole_0(A_56, A_56))), inference(superposition, [status(thm), theory('equality')], [c_379, c_22])).
% 9.55/3.96  tff(c_396, plain, (![A_56]: (k3_xboole_0(A_56, A_56)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_384])).
% 9.55/3.96  tff(c_850, plain, (![A_83, B_84, C_85]: (k2_xboole_0(k4_xboole_0(A_83, B_84), k3_xboole_0(A_83, C_85))=k4_xboole_0(A_83, k4_xboole_0(B_84, C_85)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.55/3.96  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.55/3.96  tff(c_4425, plain, (![A_170, C_171, B_172]: (k2_xboole_0(k3_xboole_0(A_170, C_171), k4_xboole_0(A_170, B_172))=k4_xboole_0(A_170, k4_xboole_0(B_172, C_171)))), inference(superposition, [status(thm), theory('equality')], [c_850, c_2])).
% 9.55/3.96  tff(c_4554, plain, (![A_56, B_172]: (k4_xboole_0(A_56, k4_xboole_0(B_172, A_56))=k2_xboole_0(A_56, k4_xboole_0(A_56, B_172)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_4425])).
% 9.55/3.96  tff(c_4633, plain, (![A_173, B_174]: (k4_xboole_0(A_173, k4_xboole_0(B_174, A_173))=A_173)), inference(demodulation, [status(thm), theory('equality')], [c_2052, c_4554])).
% 9.55/3.96  tff(c_4804, plain, (![A_173, B_174]: (k3_xboole_0(A_173, k4_xboole_0(B_174, A_173))=k4_xboole_0(A_173, A_173))), inference(superposition, [status(thm), theory('equality')], [c_4633, c_22])).
% 9.55/3.96  tff(c_5110, plain, (![A_177, B_178]: (k3_xboole_0(A_177, k4_xboole_0(B_178, A_177))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_349, c_4804])).
% 9.55/3.96  tff(c_10, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), k3_xboole_0(A_7, B_8)) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.55/3.96  tff(c_5206, plain, (![A_177, B_178]: (r2_hidden('#skF_1'(A_177, k4_xboole_0(B_178, A_177)), k1_xboole_0) | r1_xboole_0(A_177, k4_xboole_0(B_178, A_177)))), inference(superposition, [status(thm), theory('equality')], [c_5110, c_10])).
% 9.55/3.96  tff(c_5330, plain, (![A_177, B_178]: (r1_xboole_0(A_177, k4_xboole_0(B_178, A_177)))), inference(negUnitSimplification, [status(thm)], [c_559, c_5206])).
% 9.55/3.96  tff(c_30, plain, (![A_24, C_26, B_25]: (r1_xboole_0(A_24, C_26) | ~r1_xboole_0(A_24, k2_xboole_0(B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.55/3.96  tff(c_6752, plain, (![A_202, A_203, C_204, B_205]: (r1_xboole_0(A_202, k3_xboole_0(A_203, C_204)) | ~r1_xboole_0(A_202, k4_xboole_0(A_203, k4_xboole_0(B_205, C_204))))), inference(superposition, [status(thm), theory('equality')], [c_850, c_30])).
% 9.55/3.96  tff(c_7222, plain, (![B_211, C_212, B_213]: (r1_xboole_0(k4_xboole_0(B_211, C_212), k3_xboole_0(B_213, C_212)))), inference(resolution, [status(thm)], [c_5330, c_6752])).
% 9.55/3.96  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.55/3.96  tff(c_7367, plain, (![B_213, C_212, B_211]: (r1_xboole_0(k3_xboole_0(B_213, C_212), k4_xboole_0(B_211, C_212)))), inference(resolution, [status(thm)], [c_7222, c_8])).
% 9.55/3.96  tff(c_36, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.96  tff(c_197, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.55/3.96  tff(c_206, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_197])).
% 9.55/3.96  tff(c_350, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k3_xboole_0(A_54, B_55))=k4_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.55/3.96  tff(c_365, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_206, c_350])).
% 9.55/3.96  tff(c_376, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_365])).
% 9.55/3.96  tff(c_23269, plain, (![A_423, A_424]: (r1_xboole_0(A_423, k3_xboole_0(A_424, '#skF_3')) | ~r1_xboole_0(A_423, k4_xboole_0(A_424, '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_376, c_6752])).
% 9.55/3.96  tff(c_23461, plain, (![B_213, B_211]: (r1_xboole_0(k3_xboole_0(B_213, '#skF_2'), k3_xboole_0(B_211, '#skF_3')))), inference(resolution, [status(thm)], [c_7367, c_23269])).
% 9.55/3.96  tff(c_34, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.55/3.96  tff(c_26010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23461, c_34])).
% 9.55/3.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.96  
% 9.55/3.96  Inference rules
% 9.55/3.96  ----------------------
% 9.55/3.96  #Ref     : 0
% 9.55/3.96  #Sup     : 6487
% 9.55/3.96  #Fact    : 0
% 9.55/3.96  #Define  : 0
% 9.55/3.96  #Split   : 0
% 9.55/3.96  #Chain   : 0
% 9.55/3.96  #Close   : 0
% 9.55/3.96  
% 9.55/3.96  Ordering : KBO
% 9.55/3.96  
% 9.55/3.96  Simplification rules
% 9.55/3.96  ----------------------
% 9.55/3.96  #Subsume      : 944
% 9.55/3.96  #Demod        : 5072
% 9.55/3.96  #Tautology    : 4047
% 9.55/3.96  #SimpNegUnit  : 47
% 9.55/3.96  #BackRed      : 1
% 9.55/3.96  
% 9.55/3.96  #Partial instantiations: 0
% 9.55/3.96  #Strategies tried      : 1
% 9.55/3.96  
% 9.55/3.96  Timing (in seconds)
% 9.55/3.96  ----------------------
% 9.55/3.96  Preprocessing        : 0.28
% 9.55/3.96  Parsing              : 0.16
% 9.55/3.96  CNF conversion       : 0.02
% 9.55/3.96  Main loop            : 2.90
% 9.55/3.96  Inferencing          : 0.60
% 9.55/3.96  Reduction            : 1.55
% 9.55/3.96  Demodulation         : 1.31
% 9.55/3.96  BG Simplification    : 0.06
% 9.55/3.96  Subsumption          : 0.56
% 9.55/3.96  Abstraction          : 0.09
% 9.55/3.96  MUC search           : 0.00
% 9.55/3.96  Cooper               : 0.00
% 9.55/3.96  Total                : 3.22
% 9.55/3.96  Index Insertion      : 0.00
% 9.55/3.96  Index Deletion       : 0.00
% 9.55/3.96  Index Matching       : 0.00
% 9.55/3.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
