%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 110 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
        & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_40,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_354,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_364,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_354])).

tff(c_399,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_97,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_56,A_55] :
      ( r1_xboole_0(B_56,A_55)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_97,c_8])).

tff(c_106,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_106])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_533,plain,(
    ! [A_89,B_90,C_91] :
      ( k3_xboole_0(A_89,k2_xboole_0(B_90,C_91)) = k3_xboole_0(A_89,C_91)
      | ~ r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_102,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_38])).

tff(c_105,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_102])).

tff(c_542,plain,
    ( k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_105])).

tff(c_565,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_2,c_542])).

tff(c_569,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_103,c_565])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_569])).

tff(c_577,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_193,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | r1_xboole_0(A_66,k3_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1140,plain,(
    ! [A_129,B_130,A_131] :
      ( ~ r1_xboole_0(A_129,B_130)
      | r1_xboole_0(A_129,k3_xboole_0(A_131,B_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_1194,plain,(
    ! [A_132] :
      ( ~ r1_xboole_0(A_132,'#skF_2')
      | r1_xboole_0(A_132,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_577,c_1140])).

tff(c_1212,plain,(
    ! [A_133] :
      ( r1_xboole_0(k1_tarski('#skF_4'),A_133)
      | ~ r1_xboole_0(A_133,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1194,c_8])).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_256,plain,(
    ! [A_72,C_73,B_74] :
      ( ~ r2_hidden(A_72,C_73)
      | ~ r1_xboole_0(k2_tarski(A_72,B_74),C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_279,plain,(
    ! [A_13,C_73] :
      ( ~ r2_hidden(A_13,C_73)
      | ~ r1_xboole_0(k1_tarski(A_13),C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_256])).

tff(c_1339,plain,(
    ! [A_141] :
      ( ~ r2_hidden('#skF_4',A_141)
      | ~ r1_xboole_0(A_141,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1212,c_279])).

tff(c_1342,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1339])).

tff(c_1346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  
% 3.27/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.27/1.55  
% 3.27/1.55  %Foreground sorts:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Background operators:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Foreground operators:
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.27/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.27/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.27/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.27/1.55  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.27/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.27/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.27/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.55  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.27/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.27/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.27/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.27/1.55  
% 3.27/1.57  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.27/1.57  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.27/1.57  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.27/1.57  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.27/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.27/1.57  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.27/1.57  tff(f_41, axiom, (![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_xboole_1)).
% 3.27/1.57  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.27/1.57  tff(f_72, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.27/1.57  tff(c_40, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.57  tff(c_42, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.57  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.57  tff(c_354, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.57  tff(c_364, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_354])).
% 3.27/1.57  tff(c_399, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_364])).
% 3.27/1.57  tff(c_97, plain, (![A_55, B_56]: (r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.57  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.27/1.57  tff(c_103, plain, (![B_56, A_55]: (r1_xboole_0(B_56, A_55) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_8])).
% 3.27/1.57  tff(c_106, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.57  tff(c_118, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_106])).
% 3.27/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.27/1.57  tff(c_533, plain, (![A_89, B_90, C_91]: (k3_xboole_0(A_89, k2_xboole_0(B_90, C_91))=k3_xboole_0(A_89, C_91) | ~r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.27/1.57  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.27/1.57  tff(c_102, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_97, c_38])).
% 3.27/1.57  tff(c_105, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_102])).
% 3.27/1.57  tff(c_542, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_533, c_105])).
% 3.27/1.57  tff(c_565, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_2, c_542])).
% 3.27/1.57  tff(c_569, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_103, c_565])).
% 3.27/1.57  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_569])).
% 3.27/1.57  tff(c_577, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_364])).
% 3.27/1.57  tff(c_193, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | r1_xboole_0(A_66, k3_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.27/1.57  tff(c_1140, plain, (![A_129, B_130, A_131]: (~r1_xboole_0(A_129, B_130) | r1_xboole_0(A_129, k3_xboole_0(A_131, B_130)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_193])).
% 3.27/1.57  tff(c_1194, plain, (![A_132]: (~r1_xboole_0(A_132, '#skF_2') | r1_xboole_0(A_132, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_577, c_1140])).
% 3.27/1.57  tff(c_1212, plain, (![A_133]: (r1_xboole_0(k1_tarski('#skF_4'), A_133) | ~r1_xboole_0(A_133, '#skF_2'))), inference(resolution, [status(thm)], [c_1194, c_8])).
% 3.27/1.57  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.57  tff(c_256, plain, (![A_72, C_73, B_74]: (~r2_hidden(A_72, C_73) | ~r1_xboole_0(k2_tarski(A_72, B_74), C_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.27/1.57  tff(c_279, plain, (![A_13, C_73]: (~r2_hidden(A_13, C_73) | ~r1_xboole_0(k1_tarski(A_13), C_73))), inference(superposition, [status(thm), theory('equality')], [c_14, c_256])).
% 3.27/1.57  tff(c_1339, plain, (![A_141]: (~r2_hidden('#skF_4', A_141) | ~r1_xboole_0(A_141, '#skF_2'))), inference(resolution, [status(thm)], [c_1212, c_279])).
% 3.27/1.57  tff(c_1342, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1339])).
% 3.27/1.57  tff(c_1346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1342])).
% 3.27/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.57  
% 3.27/1.57  Inference rules
% 3.27/1.57  ----------------------
% 3.27/1.57  #Ref     : 0
% 3.27/1.57  #Sup     : 314
% 3.27/1.57  #Fact    : 0
% 3.27/1.57  #Define  : 0
% 3.27/1.57  #Split   : 2
% 3.27/1.57  #Chain   : 0
% 3.27/1.57  #Close   : 0
% 3.27/1.57  
% 3.27/1.57  Ordering : KBO
% 3.27/1.57  
% 3.27/1.57  Simplification rules
% 3.27/1.57  ----------------------
% 3.27/1.57  #Subsume      : 40
% 3.27/1.57  #Demod        : 89
% 3.27/1.57  #Tautology    : 124
% 3.27/1.57  #SimpNegUnit  : 0
% 3.27/1.57  #BackRed      : 3
% 3.27/1.57  
% 3.27/1.57  #Partial instantiations: 0
% 3.27/1.57  #Strategies tried      : 1
% 3.27/1.57  
% 3.27/1.57  Timing (in seconds)
% 3.27/1.57  ----------------------
% 3.27/1.57  Preprocessing        : 0.32
% 3.27/1.57  Parsing              : 0.17
% 3.27/1.57  CNF conversion       : 0.02
% 3.27/1.57  Main loop            : 0.42
% 3.27/1.57  Inferencing          : 0.15
% 3.27/1.57  Reduction            : 0.14
% 3.27/1.57  Demodulation         : 0.10
% 3.27/1.57  BG Simplification    : 0.02
% 3.27/1.57  Subsumption          : 0.08
% 3.27/1.57  Abstraction          : 0.02
% 3.27/1.57  MUC search           : 0.00
% 3.27/1.57  Cooper               : 0.00
% 3.27/1.57  Total                : 0.77
% 3.27/1.57  Index Insertion      : 0.00
% 3.27/1.57  Index Deletion       : 0.00
% 3.27/1.57  Index Matching       : 0.00
% 3.27/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
