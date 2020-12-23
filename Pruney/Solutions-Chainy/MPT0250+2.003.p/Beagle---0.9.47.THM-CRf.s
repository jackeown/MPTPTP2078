%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   69 (  75 expanded)
%              Number of leaves         :   36 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 (  93 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_94,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_103,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_82,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_98,plain,(
    ! [E_49,B_50,C_51] : r2_hidden(E_49,k1_enumset1(E_49,B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_102,plain,(
    ! [E_49,B_50,C_51] : ~ v1_xboole_0(k1_enumset1(E_49,B_50,C_51)) ),
    inference(resolution,[status(thm)],[c_98,c_4])).

tff(c_205,plain,(
    ! [A_68,B_69] : ~ v1_xboole_0(k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_102])).

tff(c_211,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_205])).

tff(c_40,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [B_25,A_24] : k2_tarski(B_25,A_24) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_254,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_306,plain,(
    ! [B_86,A_87] : k3_tarski(k2_tarski(B_86,A_87)) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_254])).

tff(c_80,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_312,plain,(
    ! [B_86,A_87] : k2_xboole_0(B_86,A_87) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_80])).

tff(c_84,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_347,plain,(
    r1_tarski(k2_xboole_0('#skF_7',k1_tarski('#skF_6')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_84])).

tff(c_401,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_403,plain,
    ( k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(resolution,[status(thm)],[c_347,c_401])).

tff(c_414,plain,(
    k2_xboole_0('#skF_7',k1_tarski('#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_403])).

tff(c_78,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_475,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_xboole_0(A_105,C_106)
      | ~ r1_xboole_0(A_105,k2_xboole_0(B_107,C_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_639,plain,(
    ! [A_133,C_134,B_135] :
      ( r1_xboole_0(k1_tarski(A_133),C_134)
      | r2_hidden(A_133,k2_xboole_0(B_135,C_134)) ) ),
    inference(resolution,[status(thm)],[c_78,c_475])).

tff(c_656,plain,(
    ! [A_136] :
      ( r1_xboole_0(k1_tarski(A_136),k1_tarski('#skF_6'))
      | r2_hidden(A_136,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_639])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = A_22
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_660,plain,(
    ! [A_136] :
      ( k4_xboole_0(k1_tarski(A_136),k1_tarski('#skF_6')) = k1_tarski(A_136)
      | r2_hidden(A_136,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_656,c_42])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_463,plain,(
    ! [D_99,A_100,B_101] :
      ( r2_hidden(D_99,A_100)
      | ~ r2_hidden(D_99,k4_xboole_0(A_100,B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_995,plain,(
    ! [A_176,B_177] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_176,B_177)),A_176)
      | v1_xboole_0(k4_xboole_0(A_176,B_177)) ) ),
    inference(resolution,[status(thm)],[c_6,c_463])).

tff(c_469,plain,(
    ! [D_102,B_103,A_104] :
      ( ~ r2_hidden(D_102,B_103)
      | ~ r2_hidden(D_102,k4_xboole_0(A_104,B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_474,plain,(
    ! [A_104,B_103] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_104,B_103)),B_103)
      | v1_xboole_0(k4_xboole_0(A_104,B_103)) ) ),
    inference(resolution,[status(thm)],[c_6,c_469])).

tff(c_1049,plain,(
    ! [A_181] : v1_xboole_0(k4_xboole_0(A_181,A_181)) ),
    inference(resolution,[status(thm)],[c_995,c_474])).

tff(c_1055,plain,
    ( v1_xboole_0(k1_tarski('#skF_6'))
    | r2_hidden('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_1049])).

tff(c_1070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_211,c_1055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/2.09  
% 4.12/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/2.10  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_3
% 4.12/2.10  
% 4.12/2.10  %Foreground sorts:
% 4.12/2.10  
% 4.12/2.10  
% 4.12/2.10  %Background operators:
% 4.12/2.10  
% 4.12/2.10  
% 4.12/2.10  %Foreground operators:
% 4.12/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/2.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/2.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.12/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.12/2.10  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.12/2.10  tff('#skF_7', type, '#skF_7': $i).
% 4.12/2.10  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.12/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/2.10  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.12/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.12/2.10  tff('#skF_6', type, '#skF_6': $i).
% 4.12/2.10  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.12/2.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.12/2.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.12/2.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.12/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/2.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.12/2.10  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.12/2.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.12/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.12/2.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/2.10  
% 4.18/2.12  tff(f_108, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.18/2.12  tff(f_92, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.18/2.12  tff(f_94, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.18/2.12  tff(f_90, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.18/2.12  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.18/2.12  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.18/2.12  tff(f_75, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.18/2.12  tff(f_103, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.18/2.12  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.18/2.12  tff(f_101, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.18/2.12  tff(f_67, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.18/2.12  tff(f_73, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.18/2.12  tff(f_43, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.18/2.12  tff(c_82, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.18/2.12  tff(c_72, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.18/2.12  tff(c_185, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.18/2.12  tff(c_98, plain, (![E_49, B_50, C_51]: (r2_hidden(E_49, k1_enumset1(E_49, B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.18/2.12  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.18/2.12  tff(c_102, plain, (![E_49, B_50, C_51]: (~v1_xboole_0(k1_enumset1(E_49, B_50, C_51)))), inference(resolution, [status(thm)], [c_98, c_4])).
% 4.18/2.12  tff(c_205, plain, (![A_68, B_69]: (~v1_xboole_0(k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_185, c_102])).
% 4.18/2.12  tff(c_211, plain, (![A_33]: (~v1_xboole_0(k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_205])).
% 4.18/2.12  tff(c_40, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.18/2.12  tff(c_46, plain, (![B_25, A_24]: (k2_tarski(B_25, A_24)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.18/2.12  tff(c_254, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.18/2.12  tff(c_306, plain, (![B_86, A_87]: (k3_tarski(k2_tarski(B_86, A_87))=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_46, c_254])).
% 4.18/2.12  tff(c_80, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.18/2.12  tff(c_312, plain, (![B_86, A_87]: (k2_xboole_0(B_86, A_87)=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_306, c_80])).
% 4.18/2.12  tff(c_84, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.18/2.12  tff(c_347, plain, (r1_tarski(k2_xboole_0('#skF_7', k1_tarski('#skF_6')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_312, c_84])).
% 4.18/2.12  tff(c_401, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~r1_tarski(A_95, B_94))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.18/2.12  tff(c_403, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_347, c_401])).
% 4.18/2.12  tff(c_414, plain, (k2_xboole_0('#skF_7', k1_tarski('#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_403])).
% 4.18/2.12  tff(c_78, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.18/2.12  tff(c_475, plain, (![A_105, C_106, B_107]: (r1_xboole_0(A_105, C_106) | ~r1_xboole_0(A_105, k2_xboole_0(B_107, C_106)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.18/2.12  tff(c_639, plain, (![A_133, C_134, B_135]: (r1_xboole_0(k1_tarski(A_133), C_134) | r2_hidden(A_133, k2_xboole_0(B_135, C_134)))), inference(resolution, [status(thm)], [c_78, c_475])).
% 4.18/2.12  tff(c_656, plain, (![A_136]: (r1_xboole_0(k1_tarski(A_136), k1_tarski('#skF_6')) | r2_hidden(A_136, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_639])).
% 4.18/2.12  tff(c_42, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=A_22 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.18/2.12  tff(c_660, plain, (![A_136]: (k4_xboole_0(k1_tarski(A_136), k1_tarski('#skF_6'))=k1_tarski(A_136) | r2_hidden(A_136, '#skF_7'))), inference(resolution, [status(thm)], [c_656, c_42])).
% 4.18/2.12  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.18/2.12  tff(c_463, plain, (![D_99, A_100, B_101]: (r2_hidden(D_99, A_100) | ~r2_hidden(D_99, k4_xboole_0(A_100, B_101)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/2.12  tff(c_995, plain, (![A_176, B_177]: (r2_hidden('#skF_1'(k4_xboole_0(A_176, B_177)), A_176) | v1_xboole_0(k4_xboole_0(A_176, B_177)))), inference(resolution, [status(thm)], [c_6, c_463])).
% 4.18/2.12  tff(c_469, plain, (![D_102, B_103, A_104]: (~r2_hidden(D_102, B_103) | ~r2_hidden(D_102, k4_xboole_0(A_104, B_103)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.18/2.12  tff(c_474, plain, (![A_104, B_103]: (~r2_hidden('#skF_1'(k4_xboole_0(A_104, B_103)), B_103) | v1_xboole_0(k4_xboole_0(A_104, B_103)))), inference(resolution, [status(thm)], [c_6, c_469])).
% 4.18/2.12  tff(c_1049, plain, (![A_181]: (v1_xboole_0(k4_xboole_0(A_181, A_181)))), inference(resolution, [status(thm)], [c_995, c_474])).
% 4.18/2.12  tff(c_1055, plain, (v1_xboole_0(k1_tarski('#skF_6')) | r2_hidden('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_660, c_1049])).
% 4.18/2.12  tff(c_1070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_211, c_1055])).
% 4.18/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/2.12  
% 4.18/2.12  Inference rules
% 4.18/2.12  ----------------------
% 4.18/2.12  #Ref     : 0
% 4.18/2.12  #Sup     : 248
% 4.18/2.12  #Fact    : 0
% 4.18/2.12  #Define  : 0
% 4.18/2.12  #Split   : 2
% 4.18/2.12  #Chain   : 0
% 4.18/2.12  #Close   : 0
% 4.18/2.12  
% 4.18/2.12  Ordering : KBO
% 4.18/2.12  
% 4.18/2.12  Simplification rules
% 4.18/2.12  ----------------------
% 4.18/2.12  #Subsume      : 59
% 4.18/2.12  #Demod        : 32
% 4.18/2.12  #Tautology    : 109
% 4.18/2.12  #SimpNegUnit  : 2
% 4.18/2.12  #BackRed      : 2
% 4.18/2.12  
% 4.18/2.12  #Partial instantiations: 0
% 4.18/2.12  #Strategies tried      : 1
% 4.18/2.12  
% 4.18/2.12  Timing (in seconds)
% 4.18/2.12  ----------------------
% 4.18/2.13  Preprocessing        : 0.54
% 4.18/2.13  Parsing              : 0.26
% 4.18/2.13  CNF conversion       : 0.04
% 4.18/2.13  Main loop            : 0.65
% 4.18/2.13  Inferencing          : 0.23
% 4.18/2.13  Reduction            : 0.22
% 4.18/2.13  Demodulation         : 0.16
% 4.18/2.13  BG Simplification    : 0.04
% 4.18/2.13  Subsumption          : 0.13
% 4.18/2.13  Abstraction          : 0.04
% 4.18/2.13  MUC search           : 0.00
% 4.18/2.13  Cooper               : 0.00
% 4.18/2.13  Total                : 1.24
% 4.18/2.13  Index Insertion      : 0.00
% 4.18/2.13  Index Deletion       : 0.00
% 4.18/2.13  Index Matching       : 0.00
% 4.18/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
