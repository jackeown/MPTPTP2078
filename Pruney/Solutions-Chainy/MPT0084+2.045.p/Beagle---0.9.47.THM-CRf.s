%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :   57 (  69 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 (  97 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_113,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(A_39,B_40)
      | k3_xboole_0(A_39,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_124,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_32])).

tff(c_18,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_175,plain,(
    ! [A_17] : k2_xboole_0(k1_xboole_0,A_17) = A_17 ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_24,plain,(
    ! [A_24] : r1_xboole_0(A_24,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_95,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_112,plain,(
    ! [A_24] : k3_xboole_0(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_950,plain,(
    ! [A_91,B_92,C_93] : r1_tarski(k2_xboole_0(k3_xboole_0(A_91,B_92),k3_xboole_0(A_91,C_93)),k2_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_979,plain,(
    ! [A_91,A_17] : r1_tarski(k2_xboole_0(k3_xboole_0(A_91,k1_xboole_0),k3_xboole_0(A_91,A_17)),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_950])).

tff(c_1020,plain,(
    ! [A_91,A_17] : r1_tarski(k3_xboole_0(A_91,A_17),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_112,c_979])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    ! [A_7,B_8] : k3_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k3_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_10,c_52])).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_467,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_494,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,'#skF_3')
      | ~ r1_tarski(A_67,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_467])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_559,plain,(
    ! [A_71] :
      ( k3_xboole_0(A_71,'#skF_3') = A_71
      | ~ r1_tarski(A_71,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_494,c_16])).

tff(c_573,plain,(
    ! [B_8] : k3_xboole_0(k3_xboole_0('#skF_1',B_8),'#skF_3') = k3_xboole_0('#skF_1',B_8) ),
    inference(resolution,[status(thm)],[c_10,c_559])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(k3_xboole_0(A_12,C_14),k3_xboole_0(B_13,C_14))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [B_31,A_32] :
      ( r1_xboole_0(B_31,A_32)
      | ~ r1_xboole_0(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    r1_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_36])).

tff(c_342,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_xboole_0(A_53,C_54)
      | ~ r1_xboole_0(B_55,C_54)
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_799,plain,(
    ! [A_86] :
      ( r1_xboole_0(A_86,'#skF_1')
      | ~ r1_tarski(A_86,k3_xboole_0('#skF_2','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_41,c_342])).

tff(c_3101,plain,(
    ! [A_156] :
      ( r1_xboole_0(k3_xboole_0(A_156,'#skF_3'),'#skF_1')
      | ~ r1_tarski(A_156,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_799])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23456,plain,(
    ! [A_417] :
      ( k3_xboole_0(k3_xboole_0(A_417,'#skF_3'),'#skF_1') = k1_xboole_0
      | ~ r1_tarski(A_417,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3101,c_2])).

tff(c_23842,plain,(
    ! [B_8] :
      ( k3_xboole_0(k3_xboole_0('#skF_1',B_8),'#skF_1') = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_1',B_8),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_23456])).

tff(c_35458,plain,(
    ! [B_538] :
      ( k3_xboole_0('#skF_1',B_538) = k1_xboole_0
      | ~ r1_tarski(k3_xboole_0('#skF_1',B_538),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_23842])).

tff(c_35525,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1020,c_35458])).

tff(c_35567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_35525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.69/5.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/5.07  
% 11.69/5.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.84/5.07  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 11.84/5.07  
% 11.84/5.07  %Foreground sorts:
% 11.84/5.07  
% 11.84/5.07  
% 11.84/5.07  %Background operators:
% 11.84/5.07  
% 11.84/5.07  
% 11.84/5.07  %Foreground operators:
% 11.84/5.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.84/5.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.84/5.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.84/5.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.84/5.07  tff('#skF_2', type, '#skF_2': $i).
% 11.84/5.07  tff('#skF_3', type, '#skF_3': $i).
% 11.84/5.07  tff('#skF_1', type, '#skF_1': $i).
% 11.84/5.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.84/5.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.84/5.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.84/5.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.84/5.07  
% 11.84/5.09  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.84/5.09  tff(f_80, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 11.84/5.09  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.84/5.09  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.84/5.09  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.84/5.09  tff(f_57, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 11.84/5.09  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 11.84/5.09  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.84/5.09  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 11.84/5.09  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_xboole_1)).
% 11.84/5.09  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.84/5.09  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.84/5.09  tff(c_113, plain, (![A_39, B_40]: (r1_xboole_0(A_39, B_40) | k3_xboole_0(A_39, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.84/5.09  tff(c_32, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.84/5.09  tff(c_124, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_113, c_32])).
% 11.84/5.09  tff(c_18, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.84/5.09  tff(c_160, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.84/5.09  tff(c_175, plain, (![A_17]: (k2_xboole_0(k1_xboole_0, A_17)=A_17)), inference(resolution, [status(thm)], [c_18, c_160])).
% 11.84/5.09  tff(c_24, plain, (![A_24]: (r1_xboole_0(A_24, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.84/5.09  tff(c_95, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.84/5.09  tff(c_112, plain, (![A_24]: (k3_xboole_0(A_24, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_95])).
% 11.84/5.09  tff(c_950, plain, (![A_91, B_92, C_93]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_91, B_92), k3_xboole_0(A_91, C_93)), k2_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.84/5.09  tff(c_979, plain, (![A_91, A_17]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_91, k1_xboole_0), k3_xboole_0(A_91, A_17)), A_17))), inference(superposition, [status(thm), theory('equality')], [c_175, c_950])).
% 11.84/5.09  tff(c_1020, plain, (![A_91, A_17]: (r1_tarski(k3_xboole_0(A_91, A_17), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_112, c_979])).
% 11.84/5.09  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.84/5.09  tff(c_52, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.84/5.09  tff(c_62, plain, (![A_7, B_8]: (k3_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k3_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_10, c_52])).
% 11.84/5.09  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.84/5.09  tff(c_467, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.84/5.09  tff(c_494, plain, (![A_67]: (r1_tarski(A_67, '#skF_3') | ~r1_tarski(A_67, '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_467])).
% 11.84/5.09  tff(c_16, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.84/5.09  tff(c_559, plain, (![A_71]: (k3_xboole_0(A_71, '#skF_3')=A_71 | ~r1_tarski(A_71, '#skF_1'))), inference(resolution, [status(thm)], [c_494, c_16])).
% 11.84/5.09  tff(c_573, plain, (![B_8]: (k3_xboole_0(k3_xboole_0('#skF_1', B_8), '#skF_3')=k3_xboole_0('#skF_1', B_8))), inference(resolution, [status(thm)], [c_10, c_559])).
% 11.84/5.09  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(k3_xboole_0(A_12, C_14), k3_xboole_0(B_13, C_14)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.84/5.09  tff(c_28, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.84/5.09  tff(c_36, plain, (![B_31, A_32]: (r1_xboole_0(B_31, A_32) | ~r1_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.84/5.09  tff(c_41, plain, (r1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_28, c_36])).
% 11.84/5.09  tff(c_342, plain, (![A_53, C_54, B_55]: (r1_xboole_0(A_53, C_54) | ~r1_xboole_0(B_55, C_54) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.84/5.09  tff(c_799, plain, (![A_86]: (r1_xboole_0(A_86, '#skF_1') | ~r1_tarski(A_86, k3_xboole_0('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_41, c_342])).
% 11.84/5.09  tff(c_3101, plain, (![A_156]: (r1_xboole_0(k3_xboole_0(A_156, '#skF_3'), '#skF_1') | ~r1_tarski(A_156, '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_799])).
% 11.84/5.09  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.84/5.09  tff(c_23456, plain, (![A_417]: (k3_xboole_0(k3_xboole_0(A_417, '#skF_3'), '#skF_1')=k1_xboole_0 | ~r1_tarski(A_417, '#skF_2'))), inference(resolution, [status(thm)], [c_3101, c_2])).
% 11.84/5.09  tff(c_23842, plain, (![B_8]: (k3_xboole_0(k3_xboole_0('#skF_1', B_8), '#skF_1')=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_1', B_8), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_23456])).
% 11.84/5.09  tff(c_35458, plain, (![B_538]: (k3_xboole_0('#skF_1', B_538)=k1_xboole_0 | ~r1_tarski(k3_xboole_0('#skF_1', B_538), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_23842])).
% 11.84/5.09  tff(c_35525, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1020, c_35458])).
% 11.84/5.09  tff(c_35567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_35525])).
% 11.84/5.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.84/5.09  
% 11.84/5.09  Inference rules
% 11.84/5.09  ----------------------
% 11.84/5.09  #Ref     : 0
% 11.84/5.09  #Sup     : 8983
% 11.84/5.09  #Fact    : 0
% 11.84/5.09  #Define  : 0
% 11.84/5.09  #Split   : 8
% 11.84/5.09  #Chain   : 0
% 11.84/5.09  #Close   : 0
% 11.84/5.09  
% 11.84/5.09  Ordering : KBO
% 11.84/5.09  
% 11.84/5.09  Simplification rules
% 11.84/5.09  ----------------------
% 11.84/5.09  #Subsume      : 1694
% 11.84/5.09  #Demod        : 7373
% 11.84/5.09  #Tautology    : 5031
% 11.84/5.09  #SimpNegUnit  : 64
% 11.84/5.09  #BackRed      : 1
% 11.84/5.09  
% 11.84/5.09  #Partial instantiations: 0
% 11.84/5.09  #Strategies tried      : 1
% 11.84/5.09  
% 11.84/5.09  Timing (in seconds)
% 11.84/5.09  ----------------------
% 11.84/5.09  Preprocessing        : 0.27
% 11.84/5.09  Parsing              : 0.15
% 11.84/5.09  CNF conversion       : 0.02
% 11.84/5.09  Main loop            : 4.04
% 11.84/5.09  Inferencing          : 0.75
% 11.84/5.09  Reduction            : 1.98
% 11.84/5.09  Demodulation         : 1.64
% 11.84/5.09  BG Simplification    : 0.07
% 11.84/5.09  Subsumption          : 1.04
% 11.84/5.09  Abstraction          : 0.11
% 11.84/5.09  MUC search           : 0.00
% 11.84/5.09  Cooper               : 0.00
% 11.84/5.09  Total                : 4.34
% 11.84/5.09  Index Insertion      : 0.00
% 11.84/5.09  Index Deletion       : 0.00
% 11.84/5.09  Index Matching       : 0.00
% 11.84/5.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
