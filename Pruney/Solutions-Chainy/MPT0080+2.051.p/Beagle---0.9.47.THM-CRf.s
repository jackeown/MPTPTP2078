%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   49 (  53 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   63 (  73 expanded)
%              Number of equality atoms :   18 (  20 expanded)
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

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_60,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_110,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | k4_xboole_0(A_37,B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_118,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_28])).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_527,plain,(
    ! [A_73,C_74,B_75] :
      ( r1_xboole_0(A_73,C_74)
      | ~ r1_xboole_0(B_75,C_74)
      | ~ r1_tarski(A_73,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_539,plain,(
    ! [A_73] :
      ( r1_xboole_0(A_73,'#skF_5')
      | ~ r1_tarski(A_73,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_527])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_310,plain,(
    ! [A_52,B_53,C_54] :
      ( ~ r1_xboole_0(A_52,B_53)
      | ~ r2_hidden(C_54,k3_xboole_0(A_52,B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_498,plain,(
    ! [A_70,B_71,B_72] :
      ( ~ r1_xboole_0(A_70,B_71)
      | r1_tarski(k3_xboole_0(A_70,B_71),B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_310])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k4_xboole_0(B_20,A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1096,plain,(
    ! [A_119,B_120] :
      ( k3_xboole_0(A_119,B_120) = k1_xboole_0
      | ~ r1_xboole_0(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_498,c_22])).

tff(c_1310,plain,(
    ! [A_126] :
      ( k3_xboole_0(A_126,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_126,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_539,c_1096])).

tff(c_1342,plain,(
    ! [B_18] : k3_xboole_0(k4_xboole_0('#skF_3',B_18),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_1310])).

tff(c_32,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_790,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_tarski(k4_xboole_0(A_96,B_97),C_98)
      | ~ r1_tarski(A_96,k2_xboole_0(B_97,C_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1945,plain,(
    ! [A_159,B_160,C_161] :
      ( k4_xboole_0(k4_xboole_0(A_159,B_160),C_161) = k1_xboole_0
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,C_161)) ) ),
    inference(resolution,[status(thm)],[c_790,c_16])).

tff(c_1985,plain,(
    k4_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_1945])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,B_40) = A_39
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_2007,plain,(
    k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),'#skF_5') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1985,c_154])).

tff(c_2035,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1342,c_2007])).

tff(c_2037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_2035])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.58  
% 3.37/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.37/1.58  
% 3.37/1.58  %Foreground sorts:
% 3.37/1.58  
% 3.37/1.58  
% 3.37/1.58  %Background operators:
% 3.37/1.58  
% 3.37/1.58  
% 3.37/1.58  %Foreground operators:
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.37/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.37/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.37/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.58  
% 3.37/1.60  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.37/1.60  tff(f_81, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 3.37/1.60  tff(f_60, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.37/1.60  tff(f_74, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.37/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.37/1.60  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.37/1.60  tff(f_64, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.37/1.60  tff(f_68, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.37/1.60  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.37/1.60  tff(c_110, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | k4_xboole_0(A_37, B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.60  tff(c_28, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.60  tff(c_118, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_110, c_28])).
% 3.37/1.60  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.37/1.60  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.60  tff(c_527, plain, (![A_73, C_74, B_75]: (r1_xboole_0(A_73, C_74) | ~r1_xboole_0(B_75, C_74) | ~r1_tarski(A_73, B_75))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.37/1.60  tff(c_539, plain, (![A_73]: (r1_xboole_0(A_73, '#skF_5') | ~r1_tarski(A_73, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_527])).
% 3.37/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.37/1.60  tff(c_310, plain, (![A_52, B_53, C_54]: (~r1_xboole_0(A_52, B_53) | ~r2_hidden(C_54, k3_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.60  tff(c_498, plain, (![A_70, B_71, B_72]: (~r1_xboole_0(A_70, B_71) | r1_tarski(k3_xboole_0(A_70, B_71), B_72))), inference(resolution, [status(thm)], [c_6, c_310])).
% 3.37/1.60  tff(c_22, plain, (![A_19, B_20]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k4_xboole_0(B_20, A_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.37/1.60  tff(c_1096, plain, (![A_119, B_120]: (k3_xboole_0(A_119, B_120)=k1_xboole_0 | ~r1_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_498, c_22])).
% 3.37/1.60  tff(c_1310, plain, (![A_126]: (k3_xboole_0(A_126, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_126, '#skF_3'))), inference(resolution, [status(thm)], [c_539, c_1096])).
% 3.37/1.60  tff(c_1342, plain, (![B_18]: (k3_xboole_0(k4_xboole_0('#skF_3', B_18), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1310])).
% 3.37/1.60  tff(c_32, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.60  tff(c_790, plain, (![A_96, B_97, C_98]: (r1_tarski(k4_xboole_0(A_96, B_97), C_98) | ~r1_tarski(A_96, k2_xboole_0(B_97, C_98)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.37/1.60  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k1_xboole_0 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.60  tff(c_1945, plain, (![A_159, B_160, C_161]: (k4_xboole_0(k4_xboole_0(A_159, B_160), C_161)=k1_xboole_0 | ~r1_tarski(A_159, k2_xboole_0(B_160, C_161)))), inference(resolution, [status(thm)], [c_790, c_16])).
% 3.37/1.60  tff(c_1985, plain, (k4_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_1945])).
% 3.37/1.60  tff(c_14, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.37/1.60  tff(c_135, plain, (![A_39, B_40]: (k3_xboole_0(A_39, B_40)=A_39 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.37/1.60  tff(c_154, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_135])).
% 3.37/1.60  tff(c_2007, plain, (k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), '#skF_5')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1985, c_154])).
% 3.37/1.60  tff(c_2035, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1342, c_2007])).
% 3.37/1.60  tff(c_2037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_2035])).
% 3.37/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.60  
% 3.37/1.60  Inference rules
% 3.37/1.60  ----------------------
% 3.37/1.60  #Ref     : 0
% 3.37/1.60  #Sup     : 478
% 3.37/1.60  #Fact    : 0
% 3.37/1.60  #Define  : 0
% 3.37/1.60  #Split   : 7
% 3.37/1.60  #Chain   : 0
% 3.37/1.60  #Close   : 0
% 3.37/1.60  
% 3.37/1.60  Ordering : KBO
% 3.37/1.60  
% 3.37/1.60  Simplification rules
% 3.37/1.60  ----------------------
% 3.37/1.60  #Subsume      : 78
% 3.37/1.60  #Demod        : 193
% 3.37/1.60  #Tautology    : 220
% 3.37/1.60  #SimpNegUnit  : 12
% 3.37/1.60  #BackRed      : 0
% 3.37/1.60  
% 3.37/1.60  #Partial instantiations: 0
% 3.37/1.60  #Strategies tried      : 1
% 3.37/1.60  
% 3.37/1.60  Timing (in seconds)
% 3.37/1.60  ----------------------
% 3.37/1.60  Preprocessing        : 0.29
% 3.37/1.60  Parsing              : 0.16
% 3.37/1.60  CNF conversion       : 0.02
% 3.37/1.60  Main loop            : 0.54
% 3.37/1.60  Inferencing          : 0.20
% 3.37/1.60  Reduction            : 0.17
% 3.37/1.60  Demodulation         : 0.12
% 3.37/1.60  BG Simplification    : 0.02
% 3.37/1.60  Subsumption          : 0.11
% 3.37/1.60  Abstraction          : 0.02
% 3.37/1.60  MUC search           : 0.00
% 3.37/1.60  Cooper               : 0.00
% 3.37/1.60  Total                : 0.86
% 3.37/1.60  Index Insertion      : 0.00
% 3.37/1.60  Index Deletion       : 0.00
% 3.37/1.60  Index Matching       : 0.00
% 3.37/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
