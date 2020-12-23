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
% DateTime   : Thu Dec  3 09:45:19 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 (  96 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_80,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_92,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80,c_38])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_xboole_0(k4_xboole_0(A_11,B_12),B_12) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_xboole_0(A_13,k4_xboole_0(B_14,C_15))
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_75,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_79,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_75])).

tff(c_128,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_xboole_0(A_44,B_45)
      | ~ r1_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_691,plain,(
    ! [A_96] :
      ( r1_xboole_0(A_96,'#skF_1')
      | ~ r1_xboole_0(A_96,k4_xboole_0('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_128])).

tff(c_940,plain,(
    ! [A_105] :
      ( r1_xboole_0(A_105,'#skF_1')
      | ~ r1_xboole_0(A_105,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_691])).

tff(c_972,plain,(
    ! [A_106] : r1_xboole_0(k4_xboole_0(A_106,'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_940])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1014,plain,(
    ! [A_110] : r1_xboole_0('#skF_1',k4_xboole_0(A_110,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_972,c_2])).

tff(c_24,plain,(
    ! [B_17,A_16,C_18] :
      ( r1_xboole_0(B_17,k4_xboole_0(A_16,C_18))
      | ~ r1_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1030,plain,(
    ! [A_111] : r1_xboole_0(A_111,k4_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1014,c_24])).

tff(c_12,plain,(
    ! [A_7] :
      ( ~ r1_xboole_0(A_7,A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1038,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1030,c_12])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1038])).

tff(c_1046,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1048,plain,(
    ! [B_112,A_113] :
      ( r1_xboole_0(B_112,A_113)
      | ~ r1_xboole_0(A_113,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1053,plain,(
    ! [B_12,A_11] : r1_xboole_0(B_12,k4_xboole_0(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_20,c_1048])).

tff(c_1111,plain,(
    ! [A_120,B_121] :
      ( k2_xboole_0(A_120,B_121) = B_121
      | ~ r1_tarski(A_120,B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1123,plain,(
    k2_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1111])).

tff(c_1221,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_xboole_0(A_140,B_141)
      | ~ r1_xboole_0(A_140,k2_xboole_0(B_141,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1264,plain,(
    ! [A_144] :
      ( r1_xboole_0(A_144,'#skF_1')
      | ~ r1_xboole_0(A_144,k4_xboole_0('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_1221])).

tff(c_1288,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1053,c_1264])).

tff(c_1293,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_1288,c_2])).

tff(c_1298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1046,c_1293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:28:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.52  
% 3.03/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.52  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.03/1.52  
% 3.03/1.52  %Foreground sorts:
% 3.03/1.52  
% 3.03/1.52  
% 3.03/1.52  %Background operators:
% 3.03/1.52  
% 3.03/1.52  
% 3.03/1.52  %Foreground operators:
% 3.03/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.03/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.03/1.52  
% 3.27/1.54  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.27/1.54  tff(f_86, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.27/1.54  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.27/1.54  tff(f_71, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 3.27/1.54  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.27/1.54  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.27/1.54  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.27/1.54  tff(f_75, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 3.27/1.54  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.27/1.54  tff(c_80, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.27/1.54  tff(c_28, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.27/1.54  tff(c_38, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.27/1.54  tff(c_92, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_80, c_38])).
% 3.27/1.54  tff(c_20, plain, (![A_11, B_12]: (r1_xboole_0(k4_xboole_0(A_11, B_12), B_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.27/1.54  tff(c_22, plain, (![A_13, B_14, C_15]: (r1_xboole_0(A_13, k4_xboole_0(B_14, C_15)) | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.27/1.54  tff(c_30, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.27/1.54  tff(c_75, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.54  tff(c_79, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_75])).
% 3.27/1.54  tff(c_128, plain, (![A_44, B_45, C_46]: (r1_xboole_0(A_44, B_45) | ~r1_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.54  tff(c_691, plain, (![A_96]: (r1_xboole_0(A_96, '#skF_1') | ~r1_xboole_0(A_96, k4_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_79, c_128])).
% 3.27/1.54  tff(c_940, plain, (![A_105]: (r1_xboole_0(A_105, '#skF_1') | ~r1_xboole_0(A_105, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_691])).
% 3.27/1.54  tff(c_972, plain, (![A_106]: (r1_xboole_0(k4_xboole_0(A_106, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_940])).
% 3.27/1.54  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.54  tff(c_1014, plain, (![A_110]: (r1_xboole_0('#skF_1', k4_xboole_0(A_110, '#skF_2')))), inference(resolution, [status(thm)], [c_972, c_2])).
% 3.27/1.54  tff(c_24, plain, (![B_17, A_16, C_18]: (r1_xboole_0(B_17, k4_xboole_0(A_16, C_18)) | ~r1_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.27/1.54  tff(c_1030, plain, (![A_111]: (r1_xboole_0(A_111, k4_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1014, c_24])).
% 3.27/1.54  tff(c_12, plain, (![A_7]: (~r1_xboole_0(A_7, A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.27/1.54  tff(c_1038, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1030, c_12])).
% 3.27/1.54  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1038])).
% 3.27/1.54  tff(c_1046, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 3.27/1.54  tff(c_1048, plain, (![B_112, A_113]: (r1_xboole_0(B_112, A_113) | ~r1_xboole_0(A_113, B_112))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.27/1.54  tff(c_1053, plain, (![B_12, A_11]: (r1_xboole_0(B_12, k4_xboole_0(A_11, B_12)))), inference(resolution, [status(thm)], [c_20, c_1048])).
% 3.27/1.54  tff(c_1111, plain, (![A_120, B_121]: (k2_xboole_0(A_120, B_121)=B_121 | ~r1_tarski(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.27/1.54  tff(c_1123, plain, (k2_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1111])).
% 3.27/1.54  tff(c_1221, plain, (![A_140, B_141, C_142]: (r1_xboole_0(A_140, B_141) | ~r1_xboole_0(A_140, k2_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.27/1.54  tff(c_1264, plain, (![A_144]: (r1_xboole_0(A_144, '#skF_1') | ~r1_xboole_0(A_144, k4_xboole_0('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_1221])).
% 3.27/1.54  tff(c_1288, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1053, c_1264])).
% 3.27/1.54  tff(c_1293, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_1288, c_2])).
% 3.27/1.54  tff(c_1298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1046, c_1293])).
% 3.27/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  Inference rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Ref     : 0
% 3.27/1.54  #Sup     : 300
% 3.27/1.54  #Fact    : 0
% 3.27/1.54  #Define  : 0
% 3.27/1.54  #Split   : 2
% 3.27/1.54  #Chain   : 0
% 3.27/1.54  #Close   : 0
% 3.27/1.54  
% 3.27/1.54  Ordering : KBO
% 3.27/1.54  
% 3.27/1.54  Simplification rules
% 3.27/1.54  ----------------------
% 3.27/1.54  #Subsume      : 8
% 3.27/1.54  #Demod        : 158
% 3.27/1.54  #Tautology    : 186
% 3.27/1.54  #SimpNegUnit  : 2
% 3.27/1.54  #BackRed      : 4
% 3.27/1.54  
% 3.27/1.54  #Partial instantiations: 0
% 3.27/1.54  #Strategies tried      : 1
% 3.27/1.54  
% 3.27/1.54  Timing (in seconds)
% 3.27/1.54  ----------------------
% 3.27/1.54  Preprocessing        : 0.27
% 3.27/1.54  Parsing              : 0.15
% 3.27/1.54  CNF conversion       : 0.02
% 3.27/1.54  Main loop            : 0.50
% 3.27/1.54  Inferencing          : 0.19
% 3.27/1.54  Reduction            : 0.15
% 3.27/1.54  Demodulation         : 0.11
% 3.27/1.54  BG Simplification    : 0.02
% 3.27/1.54  Subsumption          : 0.10
% 3.27/1.54  Abstraction          : 0.02
% 3.27/1.54  MUC search           : 0.00
% 3.27/1.54  Cooper               : 0.00
% 3.27/1.54  Total                : 0.81
% 3.27/1.54  Index Insertion      : 0.00
% 3.27/1.54  Index Deletion       : 0.00
% 3.27/1.54  Index Matching       : 0.00
% 3.27/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
