%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:49 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 261 expanded)
%              Number of leaves         :   27 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 367 expanded)
%              Number of equality atoms :   35 ( 187 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_24,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_138,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_143,plain,(
    ! [A_39] : k2_xboole_0(k1_xboole_0,A_39) = A_39 ),
    inference(resolution,[status(thm)],[c_24,c_138])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_153,plain,(
    ! [A_39] : k2_xboole_0(A_39,k1_xboole_0) = A_39 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_2])).

tff(c_1374,plain,(
    ! [A_140,B_141,C_142] :
      ( r2_hidden('#skF_1'(A_140,B_141,C_142),B_141)
      | r2_hidden('#skF_1'(A_140,B_141,C_142),A_140)
      | r2_hidden('#skF_2'(A_140,B_141,C_142),C_142)
      | k2_xboole_0(A_140,B_141) = C_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_264,plain,(
    ! [A_58,B_59] : k2_xboole_0(k1_tarski(A_58),k1_tarski(B_59)) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_312,plain,(
    ! [B_68,A_69] : k2_xboole_0(k1_tarski(B_68),k1_tarski(A_69)) = k2_tarski(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_2])).

tff(c_28,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_318,plain,(
    ! [B_68,A_69] : k2_tarski(B_68,A_69) = k2_tarski(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_28])).

tff(c_60,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_78,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_44])).

tff(c_354,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_78])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( ~ r2_hidden(D_8,A_3)
      | r2_hidden(D_8,k2_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_520,plain,(
    ! [A_87,B_88,C_89] :
      ( r1_tarski(k2_tarski(A_87,B_88),C_89)
      | ~ r2_hidden(B_88,C_89)
      | ~ r2_hidden(A_87,C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_542,plain,(
    ! [A_90,C_91] :
      ( r1_tarski(k1_tarski(A_90),C_91)
      | ~ r2_hidden(A_90,C_91)
      | ~ r2_hidden(A_90,C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_520])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_551,plain,(
    ! [A_92,C_93] :
      ( k2_xboole_0(k1_tarski(A_92),C_93) = C_93
      | ~ r2_hidden(A_92,C_93) ) ),
    inference(resolution,[status(thm)],[c_542,c_22])).

tff(c_42,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_669,plain,(
    ! [C_104,A_105] :
      ( k1_xboole_0 != C_104
      | ~ r2_hidden(A_105,C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_42])).

tff(c_686,plain,(
    ! [A_106,B_107,D_108] :
      ( k2_xboole_0(A_106,B_107) != k1_xboole_0
      | ~ r2_hidden(D_108,A_106) ) ),
    inference(resolution,[status(thm)],[c_8,c_669])).

tff(c_706,plain,(
    ! [D_108] : ~ r2_hidden(D_108,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_686])).

tff(c_1723,plain,(
    ! [A_149,C_150] :
      ( r2_hidden('#skF_1'(A_149,'#skF_5',C_150),A_149)
      | r2_hidden('#skF_2'(A_149,'#skF_5',C_150),C_150)
      | k2_xboole_0(A_149,'#skF_5') = C_150 ) ),
    inference(resolution,[status(thm)],[c_1374,c_706])).

tff(c_82,plain,(
    ! [B_31,A_25] : k2_xboole_0(B_31,k1_tarski(A_25)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_42])).

tff(c_150,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_82])).

tff(c_575,plain,(
    ! [A_92] :
      ( k1_tarski(A_92) = k1_xboole_0
      | ~ r2_hidden(A_92,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_153])).

tff(c_610,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_575])).

tff(c_1767,plain,(
    ! [C_150] :
      ( r2_hidden('#skF_2'(k1_xboole_0,'#skF_5',C_150),C_150)
      | k2_xboole_0(k1_xboole_0,'#skF_5') = C_150 ) ),
    inference(resolution,[status(thm)],[c_1723,c_610])).

tff(c_1851,plain,(
    ! [C_151] :
      ( r2_hidden('#skF_2'(k1_xboole_0,'#skF_5',C_151),C_151)
      | C_151 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_2,c_1767])).

tff(c_1911,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1851,c_610])).

tff(c_1922,plain,(
    ! [A_25] : k1_tarski(A_25) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1911,c_150])).

tff(c_504,plain,(
    ! [D_83,A_84,B_85] :
      ( ~ r2_hidden(D_83,k1_tarski(A_84))
      | r2_hidden(D_83,k2_tarski(A_84,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_8])).

tff(c_218,plain,(
    ! [D_45,B_46,A_47] :
      ( ~ r2_hidden(D_45,B_46)
      | r2_hidden(D_45,k2_xboole_0(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_227,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_3','#skF_4'))
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_218])).

tff(c_450,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_4','#skF_3'))
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_227])).

tff(c_518,plain,(
    ! [D_83] :
      ( r2_hidden(D_83,k1_xboole_0)
      | ~ r2_hidden(D_83,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_504,c_450])).

tff(c_634,plain,(
    ! [D_83] : ~ r2_hidden(D_83,k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_518])).

tff(c_1910,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1851,c_634])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1922,c_1910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:03:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.66  
% 3.54/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.66  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 3.54/1.66  
% 3.54/1.66  %Foreground sorts:
% 3.54/1.66  
% 3.54/1.66  
% 3.54/1.66  %Background operators:
% 3.54/1.66  
% 3.54/1.66  
% 3.54/1.66  %Foreground operators:
% 3.54/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.54/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.54/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.54/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.54/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.54/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.54/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.54/1.66  
% 3.54/1.67  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.54/1.67  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.54/1.67  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.54/1.67  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.54/1.67  tff(f_46, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 3.54/1.67  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 3.54/1.67  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.54/1.67  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.54/1.67  tff(f_61, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.54/1.67  tff(c_24, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.54/1.67  tff(c_138, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.67  tff(c_143, plain, (![A_39]: (k2_xboole_0(k1_xboole_0, A_39)=A_39)), inference(resolution, [status(thm)], [c_24, c_138])).
% 3.54/1.67  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.67  tff(c_153, plain, (![A_39]: (k2_xboole_0(A_39, k1_xboole_0)=A_39)), inference(superposition, [status(thm), theory('equality')], [c_143, c_2])).
% 3.54/1.67  tff(c_1374, plain, (![A_140, B_141, C_142]: (r2_hidden('#skF_1'(A_140, B_141, C_142), B_141) | r2_hidden('#skF_1'(A_140, B_141, C_142), A_140) | r2_hidden('#skF_2'(A_140, B_141, C_142), C_142) | k2_xboole_0(A_140, B_141)=C_142)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.67  tff(c_264, plain, (![A_58, B_59]: (k2_xboole_0(k1_tarski(A_58), k1_tarski(B_59))=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.54/1.67  tff(c_312, plain, (![B_68, A_69]: (k2_xboole_0(k1_tarski(B_68), k1_tarski(A_69))=k2_tarski(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_264, c_2])).
% 3.54/1.67  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.54/1.67  tff(c_318, plain, (![B_68, A_69]: (k2_tarski(B_68, A_69)=k2_tarski(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_312, c_28])).
% 3.54/1.67  tff(c_60, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.67  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.54/1.67  tff(c_78, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_44])).
% 3.54/1.67  tff(c_354, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_318, c_78])).
% 3.54/1.67  tff(c_8, plain, (![D_8, A_3, B_4]: (~r2_hidden(D_8, A_3) | r2_hidden(D_8, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.67  tff(c_30, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.54/1.67  tff(c_520, plain, (![A_87, B_88, C_89]: (r1_tarski(k2_tarski(A_87, B_88), C_89) | ~r2_hidden(B_88, C_89) | ~r2_hidden(A_87, C_89))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.54/1.67  tff(c_542, plain, (![A_90, C_91]: (r1_tarski(k1_tarski(A_90), C_91) | ~r2_hidden(A_90, C_91) | ~r2_hidden(A_90, C_91))), inference(superposition, [status(thm), theory('equality')], [c_30, c_520])).
% 3.54/1.67  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.54/1.67  tff(c_551, plain, (![A_92, C_93]: (k2_xboole_0(k1_tarski(A_92), C_93)=C_93 | ~r2_hidden(A_92, C_93))), inference(resolution, [status(thm)], [c_542, c_22])).
% 3.54/1.67  tff(c_42, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.67  tff(c_669, plain, (![C_104, A_105]: (k1_xboole_0!=C_104 | ~r2_hidden(A_105, C_104))), inference(superposition, [status(thm), theory('equality')], [c_551, c_42])).
% 3.54/1.67  tff(c_686, plain, (![A_106, B_107, D_108]: (k2_xboole_0(A_106, B_107)!=k1_xboole_0 | ~r2_hidden(D_108, A_106))), inference(resolution, [status(thm)], [c_8, c_669])).
% 3.54/1.67  tff(c_706, plain, (![D_108]: (~r2_hidden(D_108, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_354, c_686])).
% 3.54/1.67  tff(c_1723, plain, (![A_149, C_150]: (r2_hidden('#skF_1'(A_149, '#skF_5', C_150), A_149) | r2_hidden('#skF_2'(A_149, '#skF_5', C_150), C_150) | k2_xboole_0(A_149, '#skF_5')=C_150)), inference(resolution, [status(thm)], [c_1374, c_706])).
% 3.54/1.67  tff(c_82, plain, (![B_31, A_25]: (k2_xboole_0(B_31, k1_tarski(A_25))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_60, c_42])).
% 3.54/1.67  tff(c_150, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_143, c_82])).
% 3.54/1.67  tff(c_575, plain, (![A_92]: (k1_tarski(A_92)=k1_xboole_0 | ~r2_hidden(A_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_551, c_153])).
% 3.54/1.67  tff(c_610, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_150, c_575])).
% 3.54/1.67  tff(c_1767, plain, (![C_150]: (r2_hidden('#skF_2'(k1_xboole_0, '#skF_5', C_150), C_150) | k2_xboole_0(k1_xboole_0, '#skF_5')=C_150)), inference(resolution, [status(thm)], [c_1723, c_610])).
% 3.54/1.67  tff(c_1851, plain, (![C_151]: (r2_hidden('#skF_2'(k1_xboole_0, '#skF_5', C_151), C_151) | C_151='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_2, c_1767])).
% 3.54/1.67  tff(c_1911, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1851, c_610])).
% 3.54/1.67  tff(c_1922, plain, (![A_25]: (k1_tarski(A_25)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1911, c_150])).
% 3.54/1.67  tff(c_504, plain, (![D_83, A_84, B_85]: (~r2_hidden(D_83, k1_tarski(A_84)) | r2_hidden(D_83, k2_tarski(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_8])).
% 3.54/1.67  tff(c_218, plain, (![D_45, B_46, A_47]: (~r2_hidden(D_45, B_46) | r2_hidden(D_45, k2_xboole_0(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.54/1.67  tff(c_227, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_3', '#skF_4')) | r2_hidden(D_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_78, c_218])).
% 3.54/1.67  tff(c_450, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_4', '#skF_3')) | r2_hidden(D_45, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_227])).
% 3.54/1.67  tff(c_518, plain, (![D_83]: (r2_hidden(D_83, k1_xboole_0) | ~r2_hidden(D_83, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_504, c_450])).
% 3.54/1.67  tff(c_634, plain, (![D_83]: (~r2_hidden(D_83, k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_610, c_518])).
% 3.54/1.67  tff(c_1910, plain, (k1_tarski('#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1851, c_634])).
% 3.54/1.67  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1922, c_1910])).
% 3.54/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.67  
% 3.54/1.67  Inference rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Ref     : 0
% 3.54/1.67  #Sup     : 459
% 3.54/1.67  #Fact    : 6
% 3.54/1.67  #Define  : 0
% 3.54/1.67  #Split   : 0
% 3.54/1.67  #Chain   : 0
% 3.54/1.67  #Close   : 0
% 3.54/1.67  
% 3.54/1.67  Ordering : KBO
% 3.54/1.67  
% 3.54/1.67  Simplification rules
% 3.54/1.67  ----------------------
% 3.54/1.67  #Subsume      : 150
% 3.54/1.67  #Demod        : 93
% 3.54/1.67  #Tautology    : 111
% 3.54/1.67  #SimpNegUnit  : 17
% 3.54/1.67  #BackRed      : 24
% 3.54/1.67  
% 3.54/1.67  #Partial instantiations: 0
% 3.54/1.67  #Strategies tried      : 1
% 3.54/1.67  
% 3.54/1.67  Timing (in seconds)
% 3.54/1.67  ----------------------
% 3.54/1.67  Preprocessing        : 0.32
% 3.54/1.67  Parsing              : 0.17
% 3.54/1.67  CNF conversion       : 0.02
% 3.54/1.68  Main loop            : 0.54
% 3.54/1.68  Inferencing          : 0.18
% 3.54/1.68  Reduction            : 0.19
% 3.54/1.68  Demodulation         : 0.14
% 3.54/1.68  BG Simplification    : 0.03
% 3.54/1.68  Subsumption          : 0.11
% 3.54/1.68  Abstraction          : 0.03
% 3.54/1.68  MUC search           : 0.00
% 3.54/1.68  Cooper               : 0.00
% 3.54/1.68  Total                : 0.89
% 3.54/1.68  Index Insertion      : 0.00
% 3.54/1.68  Index Deletion       : 0.00
% 3.54/1.68  Index Matching       : 0.00
% 3.54/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
