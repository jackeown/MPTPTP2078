%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 (  73 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_106,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_28])).

tff(c_16,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_553,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_xboole_0(A_83,C_84)
      | ~ r1_xboole_0(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_565,plain,(
    ! [A_83] :
      ( r1_xboole_0(A_83,'#skF_5')
      | ~ r1_tarski(A_83,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_553])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_354,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_524,plain,(
    ! [A_80,B_81,B_82] :
      ( ~ r1_xboole_0(A_80,B_81)
      | r1_tarski(k3_xboole_0(A_80,B_81),B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_354])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_963,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,B_118) = k1_xboole_0
      | ~ r1_xboole_0(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_524,c_22])).

tff(c_1118,plain,(
    ! [A_122] :
      ( k3_xboole_0(A_122,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_122,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_565,c_963])).

tff(c_1150,plain,(
    ! [B_16] : k3_xboole_0(k4_xboole_0('#skF_3',B_16),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_1118])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_618,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(k4_xboole_0(A_90,B_91),C_92)
      | ~ r1_tarski(A_90,k2_xboole_0(B_91,C_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1330,plain,(
    ! [A_131,B_132,C_133] :
      ( k4_xboole_0(k4_xboole_0(A_131,B_132),C_133) = k1_xboole_0
      | ~ r1_tarski(A_131,k2_xboole_0(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_618,c_20])).

tff(c_1365,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1330])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = A_35
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_106,c_14])).

tff(c_1369,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_117])).

tff(c_1394,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1369])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.64  
% 3.02/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.02/1.64  
% 3.02/1.64  %Foreground sorts:
% 3.02/1.64  
% 3.02/1.64  
% 3.02/1.64  %Background operators:
% 3.02/1.64  
% 3.02/1.64  
% 3.02/1.64  %Foreground operators:
% 3.02/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.02/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.64  
% 3.02/1.65  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.02/1.65  tff(f_81, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.02/1.65  tff(f_56, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.02/1.65  tff(f_74, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.02/1.65  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.02/1.65  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.02/1.65  tff(f_64, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.02/1.65  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.02/1.65  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.02/1.65  tff(c_106, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.65  tff(c_28, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.65  tff(c_118, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_28])).
% 3.02/1.65  tff(c_16, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.02/1.65  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.65  tff(c_553, plain, (![A_83, C_84, B_85]: (r1_xboole_0(A_83, C_84) | ~r1_xboole_0(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.02/1.65  tff(c_565, plain, (![A_83]: (r1_xboole_0(A_83, '#skF_5') | ~r1_tarski(A_83, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_553])).
% 3.02/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.02/1.65  tff(c_354, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.65  tff(c_524, plain, (![A_80, B_81, B_82]: (~r1_xboole_0(A_80, B_81) | r1_tarski(k3_xboole_0(A_80, B_81), B_82))), inference(resolution, [status(thm)], [c_6, c_354])).
% 3.02/1.65  tff(c_22, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.65  tff(c_963, plain, (![A_117, B_118]: (k3_xboole_0(A_117, B_118)=k1_xboole_0 | ~r1_xboole_0(A_117, B_118))), inference(resolution, [status(thm)], [c_524, c_22])).
% 3.02/1.65  tff(c_1118, plain, (![A_122]: (k3_xboole_0(A_122, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_122, '#skF_3'))), inference(resolution, [status(thm)], [c_565, c_963])).
% 3.02/1.65  tff(c_1150, plain, (![B_16]: (k3_xboole_0(k4_xboole_0('#skF_3', B_16), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_1118])).
% 3.02/1.65  tff(c_32, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.02/1.65  tff(c_618, plain, (![A_90, B_91, C_92]: (r1_tarski(k4_xboole_0(A_90, B_91), C_92) | ~r1_tarski(A_90, k2_xboole_0(B_91, C_92)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.02/1.65  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.02/1.65  tff(c_1330, plain, (![A_131, B_132, C_133]: (k4_xboole_0(k4_xboole_0(A_131, B_132), C_133)=k1_xboole_0 | ~r1_tarski(A_131, k2_xboole_0(B_132, C_133)))), inference(resolution, [status(thm)], [c_618, c_20])).
% 3.02/1.65  tff(c_1365, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1330])).
% 3.02/1.65  tff(c_14, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.02/1.65  tff(c_117, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=A_35 | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_106, c_14])).
% 3.02/1.65  tff(c_1369, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1365, c_117])).
% 3.02/1.65  tff(c_1394, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1369])).
% 3.02/1.65  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_1394])).
% 3.02/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.65  
% 3.02/1.65  Inference rules
% 3.02/1.65  ----------------------
% 3.02/1.65  #Ref     : 0
% 3.02/1.65  #Sup     : 335
% 3.02/1.65  #Fact    : 0
% 3.02/1.65  #Define  : 0
% 3.02/1.65  #Split   : 5
% 3.02/1.65  #Chain   : 0
% 3.02/1.65  #Close   : 0
% 3.02/1.65  
% 3.02/1.65  Ordering : KBO
% 3.02/1.65  
% 3.02/1.65  Simplification rules
% 3.02/1.65  ----------------------
% 3.02/1.65  #Subsume      : 49
% 3.02/1.65  #Demod        : 117
% 3.02/1.65  #Tautology    : 156
% 3.02/1.65  #SimpNegUnit  : 9
% 3.02/1.65  #BackRed      : 0
% 3.02/1.65  
% 3.02/1.65  #Partial instantiations: 0
% 3.02/1.65  #Strategies tried      : 1
% 3.02/1.65  
% 3.02/1.65  Timing (in seconds)
% 3.02/1.65  ----------------------
% 3.02/1.66  Preprocessing        : 0.32
% 3.02/1.66  Parsing              : 0.18
% 3.02/1.66  CNF conversion       : 0.02
% 3.02/1.66  Main loop            : 0.43
% 3.02/1.66  Inferencing          : 0.16
% 3.02/1.66  Reduction            : 0.13
% 3.02/1.66  Demodulation         : 0.09
% 3.02/1.66  BG Simplification    : 0.02
% 3.02/1.66  Subsumption          : 0.09
% 3.02/1.66  Abstraction          : 0.02
% 3.02/1.66  MUC search           : 0.00
% 3.02/1.66  Cooper               : 0.00
% 3.02/1.66  Total                : 0.77
% 3.02/1.66  Index Insertion      : 0.00
% 3.02/1.66  Index Deletion       : 0.00
% 3.02/1.66  Index Matching       : 0.00
% 3.02/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
