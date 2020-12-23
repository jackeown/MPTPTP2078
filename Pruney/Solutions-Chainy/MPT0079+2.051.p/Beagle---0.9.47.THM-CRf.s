%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   64 (  76 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  89 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_xboole_0(A,k3_xboole_0(B,C)) = k3_xboole_0(k2_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k2_xboole_0(A_30,B_31)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_71,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_64])).

tff(c_901,plain,(
    ! [A_71,B_72,C_73] : k3_xboole_0(k4_xboole_0(A_71,B_72),k4_xboole_0(A_71,C_73)) = k4_xboole_0(A_71,k2_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_981,plain,(
    ! [A_7,B_72] : k4_xboole_0(A_7,k2_xboole_0(B_72,A_7)) = k3_xboole_0(k4_xboole_0(A_7,B_72),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_901])).

tff(c_1013,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k2_xboole_0(B_75,A_74)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_981])).

tff(c_28,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1037,plain,(
    ! [A_74,B_75] : k3_xboole_0(A_74,k2_xboole_0(B_75,A_74)) = k4_xboole_0(A_74,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1013,c_28])).

tff(c_1080,plain,(
    ! [A_74,B_75] : k3_xboole_0(A_74,k2_xboole_0(B_75,A_74)) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1037])).

tff(c_34,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_102,plain,(
    ! [B_33,A_34] :
      ( r1_xboole_0(B_33,A_34)
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_107,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_123,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_107,c_123])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_143,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_227,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_248,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_227])).

tff(c_261,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_248])).

tff(c_388,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2780,plain,(
    ! [C_108] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_1',C_108)) = k4_xboole_0('#skF_3',C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_388])).

tff(c_38,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_24])).

tff(c_2830,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2780,c_94])).

tff(c_160,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_167,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | k4_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_160,c_8])).

tff(c_2927,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2830,c_167])).

tff(c_643,plain,(
    ! [A_63,B_64,C_65] : k3_xboole_0(k2_xboole_0(A_63,B_64),k2_xboole_0(A_63,C_65)) = k2_xboole_0(A_63,k3_xboole_0(B_64,C_65)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4051,plain,(
    ! [B_120] : k3_xboole_0(k2_xboole_0('#skF_3',B_120),k2_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k3_xboole_0(B_120,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_643])).

tff(c_4084,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_2')) = k2_xboole_0('#skF_3',k3_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2927,c_4051])).

tff(c_4116,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1080,c_10,c_141,c_4084])).

tff(c_4118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:23:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/2.00  
% 4.60/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.00  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.87/2.00  
% 4.87/2.00  %Foreground sorts:
% 4.87/2.00  
% 4.87/2.00  
% 4.87/2.00  %Background operators:
% 4.87/2.00  
% 4.87/2.00  
% 4.87/2.00  %Foreground operators:
% 4.87/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.87/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.87/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.87/2.00  tff('#skF_3', type, '#skF_3': $i).
% 4.87/2.00  tff('#skF_1', type, '#skF_1': $i).
% 4.87/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/2.00  tff('#skF_4', type, '#skF_4': $i).
% 4.87/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.87/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.87/2.00  
% 4.87/2.01  tff(f_68, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.87/2.01  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.87/2.01  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.87/2.01  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.87/2.01  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.87/2.01  tff(f_59, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 4.87/2.01  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.87/2.01  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.87/2.01  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.87/2.01  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.87/2.01  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.87/2.01  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 4.87/2.01  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.87/2.01  tff(f_41, axiom, (![A, B, C]: (k2_xboole_0(A, k3_xboole_0(B, C)) = k3_xboole_0(k2_xboole_0(A, B), k2_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_xboole_1)).
% 4.87/2.01  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/2.01  tff(c_20, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.87/2.01  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/2.01  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.87/2.01  tff(c_64, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k2_xboole_0(A_30, B_31))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.87/2.01  tff(c_71, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_64])).
% 4.87/2.01  tff(c_901, plain, (![A_71, B_72, C_73]: (k3_xboole_0(k4_xboole_0(A_71, B_72), k4_xboole_0(A_71, C_73))=k4_xboole_0(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.87/2.01  tff(c_981, plain, (![A_7, B_72]: (k4_xboole_0(A_7, k2_xboole_0(B_72, A_7))=k3_xboole_0(k4_xboole_0(A_7, B_72), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_901])).
% 4.87/2.01  tff(c_1013, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k2_xboole_0(B_75, A_74))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_981])).
% 4.87/2.01  tff(c_28, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.87/2.01  tff(c_1037, plain, (![A_74, B_75]: (k3_xboole_0(A_74, k2_xboole_0(B_75, A_74))=k4_xboole_0(A_74, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1013, c_28])).
% 4.87/2.01  tff(c_1080, plain, (![A_74, B_75]: (k3_xboole_0(A_74, k2_xboole_0(B_75, A_74))=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1037])).
% 4.87/2.01  tff(c_34, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/2.01  tff(c_102, plain, (![B_33, A_34]: (r1_xboole_0(B_33, A_34) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.87/2.01  tff(c_107, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_102])).
% 4.87/2.01  tff(c_123, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.87/2.01  tff(c_141, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_107, c_123])).
% 4.87/2.01  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/2.01  tff(c_143, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_123])).
% 4.87/2.01  tff(c_227, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.87/2.01  tff(c_248, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_143, c_227])).
% 4.87/2.01  tff(c_261, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_248])).
% 4.87/2.01  tff(c_388, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.87/2.01  tff(c_2780, plain, (![C_108]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', C_108))=k4_xboole_0('#skF_3', C_108))), inference(superposition, [status(thm), theory('equality')], [c_261, c_388])).
% 4.87/2.01  tff(c_38, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.87/2.01  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.87/2.01  tff(c_94, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_24])).
% 4.87/2.01  tff(c_2830, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2780, c_94])).
% 4.87/2.01  tff(c_160, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.87/2.01  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/2.01  tff(c_167, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | k4_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_160, c_8])).
% 4.87/2.01  tff(c_2927, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2830, c_167])).
% 4.87/2.01  tff(c_643, plain, (![A_63, B_64, C_65]: (k3_xboole_0(k2_xboole_0(A_63, B_64), k2_xboole_0(A_63, C_65))=k2_xboole_0(A_63, k3_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.87/2.01  tff(c_4051, plain, (![B_120]: (k3_xboole_0(k2_xboole_0('#skF_3', B_120), k2_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k3_xboole_0(B_120, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_643])).
% 4.87/2.01  tff(c_4084, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))=k2_xboole_0('#skF_3', k3_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2927, c_4051])).
% 4.87/2.01  tff(c_4116, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1080, c_10, c_141, c_4084])).
% 4.87/2.01  tff(c_4118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_4116])).
% 4.87/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/2.01  
% 4.87/2.01  Inference rules
% 4.87/2.01  ----------------------
% 4.87/2.01  #Ref     : 0
% 4.87/2.01  #Sup     : 1037
% 4.87/2.01  #Fact    : 0
% 4.87/2.01  #Define  : 0
% 4.87/2.01  #Split   : 4
% 4.87/2.01  #Chain   : 0
% 4.87/2.01  #Close   : 0
% 4.87/2.01  
% 4.87/2.01  Ordering : KBO
% 4.87/2.01  
% 4.87/2.01  Simplification rules
% 4.87/2.01  ----------------------
% 4.87/2.01  #Subsume      : 9
% 4.87/2.01  #Demod        : 850
% 4.87/2.01  #Tautology    : 728
% 4.87/2.01  #SimpNegUnit  : 4
% 4.87/2.01  #BackRed      : 0
% 4.87/2.01  
% 4.87/2.01  #Partial instantiations: 0
% 4.87/2.01  #Strategies tried      : 1
% 4.87/2.01  
% 4.87/2.01  Timing (in seconds)
% 4.87/2.01  ----------------------
% 4.87/2.02  Preprocessing        : 0.33
% 4.87/2.02  Parsing              : 0.18
% 4.87/2.02  CNF conversion       : 0.02
% 4.87/2.02  Main loop            : 0.86
% 4.87/2.02  Inferencing          : 0.30
% 4.87/2.02  Reduction            : 0.34
% 4.87/2.02  Demodulation         : 0.27
% 4.87/2.02  BG Simplification    : 0.03
% 4.87/2.02  Subsumption          : 0.13
% 4.87/2.02  Abstraction          : 0.05
% 4.87/2.02  MUC search           : 0.00
% 4.87/2.02  Cooper               : 0.00
% 4.87/2.02  Total                : 1.22
% 4.87/2.02  Index Insertion      : 0.00
% 4.87/2.02  Index Deletion       : 0.00
% 4.87/2.02  Index Matching       : 0.00
% 4.87/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
