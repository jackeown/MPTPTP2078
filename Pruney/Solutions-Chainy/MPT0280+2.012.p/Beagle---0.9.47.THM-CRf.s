%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:25 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  72 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 (  98 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_72,plain,(
    ! [A_69,B_70] : k1_enumset1(A_69,A_69,B_70) = k2_tarski(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_14,plain,(
    ! [E_20,A_14,B_15] : r2_hidden(E_20,k1_enumset1(A_14,B_15,E_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [B_70,A_69] : r2_hidden(B_70,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_14])).

tff(c_60,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,k3_tarski(B_49))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_149,plain,(
    ! [A_88,A_89,B_90] :
      ( r1_tarski(A_88,k2_xboole_0(A_89,B_90))
      | ~ r2_hidden(A_88,k2_tarski(A_89,B_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_156,plain,(
    ! [B_70,A_69] : r1_tarski(B_70,k2_xboole_0(A_69,B_70)) ),
    inference(resolution,[status(thm)],[c_81,c_149])).

tff(c_52,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(k1_zfmisc_1(A_52),k1_zfmisc_1(B_53))
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(k5_xboole_0(A_4,C_6),B_5)
      | ~ r1_tarski(C_6,B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_12,B_13] : k5_xboole_0(k5_xboole_0(A_12,B_13),k3_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [A_95,C_96,B_97] :
      ( r1_tarski(k5_xboole_0(A_95,C_96),B_97)
      | ~ r1_tarski(C_96,B_97)
      | ~ r1_tarski(A_95,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_423,plain,(
    ! [A_137,B_138,B_139] :
      ( r1_tarski(k2_xboole_0(A_137,B_138),B_139)
      | ~ r1_tarski(k3_xboole_0(A_137,B_138),B_139)
      | ~ r1_tarski(k5_xboole_0(A_137,B_138),B_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_188])).

tff(c_588,plain,(
    ! [A_150,C_151,B_152] :
      ( r1_tarski(k2_xboole_0(A_150,C_151),B_152)
      | ~ r1_tarski(k3_xboole_0(A_150,C_151),B_152)
      | ~ r1_tarski(C_151,B_152)
      | ~ r1_tarski(A_150,B_152) ) ),
    inference(resolution,[status(thm)],[c_4,c_423])).

tff(c_608,plain,(
    ! [A_153,C_154,B_155] :
      ( r1_tarski(k2_xboole_0(A_153,C_154),B_155)
      | ~ r1_tarski(C_154,B_155)
      | ~ r1_tarski(A_153,B_155) ) ),
    inference(resolution,[status(thm)],[c_2,c_588])).

tff(c_54,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'),k1_zfmisc_1('#skF_4')),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_612,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_608,c_54])).

tff(c_613,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_3'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_612])).

tff(c_616,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_613])).

tff(c_620,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_616])).

tff(c_621,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1(k2_xboole_0('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_612])).

tff(c_625,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_621])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  
% 2.67/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.38  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.67/1.38  
% 2.67/1.38  %Foreground sorts:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Background operators:
% 2.67/1.38  
% 2.67/1.38  
% 2.67/1.38  %Foreground operators:
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.67/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.67/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.67/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.67/1.38  
% 2.91/1.39  tff(f_58, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.91/1.39  tff(f_56, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.91/1.39  tff(f_74, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.91/1.39  tff(f_72, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.91/1.39  tff(f_78, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 2.91/1.39  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.91/1.39  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.91/1.39  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.91/1.39  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 2.91/1.39  tff(f_81, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 2.91/1.39  tff(c_72, plain, (![A_69, B_70]: (k1_enumset1(A_69, A_69, B_70)=k2_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.91/1.39  tff(c_14, plain, (![E_20, A_14, B_15]: (r2_hidden(E_20, k1_enumset1(A_14, B_15, E_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.91/1.39  tff(c_81, plain, (![B_70, A_69]: (r2_hidden(B_70, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_14])).
% 2.91/1.39  tff(c_60, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.91/1.39  tff(c_48, plain, (![A_48, B_49]: (r1_tarski(A_48, k3_tarski(B_49)) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.91/1.39  tff(c_149, plain, (![A_88, A_89, B_90]: (r1_tarski(A_88, k2_xboole_0(A_89, B_90)) | ~r2_hidden(A_88, k2_tarski(A_89, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_48])).
% 2.91/1.39  tff(c_156, plain, (![B_70, A_69]: (r1_tarski(B_70, k2_xboole_0(A_69, B_70)))), inference(resolution, [status(thm)], [c_81, c_149])).
% 2.91/1.39  tff(c_52, plain, (![A_52, B_53]: (r1_tarski(k1_zfmisc_1(A_52), k1_zfmisc_1(B_53)) | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.91/1.39  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.39  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.91/1.39  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(k5_xboole_0(A_4, C_6), B_5) | ~r1_tarski(C_6, B_5) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.39  tff(c_10, plain, (![A_12, B_13]: (k5_xboole_0(k5_xboole_0(A_12, B_13), k3_xboole_0(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.91/1.39  tff(c_188, plain, (![A_95, C_96, B_97]: (r1_tarski(k5_xboole_0(A_95, C_96), B_97) | ~r1_tarski(C_96, B_97) | ~r1_tarski(A_95, B_97))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.39  tff(c_423, plain, (![A_137, B_138, B_139]: (r1_tarski(k2_xboole_0(A_137, B_138), B_139) | ~r1_tarski(k3_xboole_0(A_137, B_138), B_139) | ~r1_tarski(k5_xboole_0(A_137, B_138), B_139))), inference(superposition, [status(thm), theory('equality')], [c_10, c_188])).
% 2.91/1.39  tff(c_588, plain, (![A_150, C_151, B_152]: (r1_tarski(k2_xboole_0(A_150, C_151), B_152) | ~r1_tarski(k3_xboole_0(A_150, C_151), B_152) | ~r1_tarski(C_151, B_152) | ~r1_tarski(A_150, B_152))), inference(resolution, [status(thm)], [c_4, c_423])).
% 2.91/1.39  tff(c_608, plain, (![A_153, C_154, B_155]: (r1_tarski(k2_xboole_0(A_153, C_154), B_155) | ~r1_tarski(C_154, B_155) | ~r1_tarski(A_153, B_155))), inference(resolution, [status(thm)], [c_2, c_588])).
% 2.91/1.39  tff(c_54, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_3'), k1_zfmisc_1('#skF_4')), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.91/1.39  tff(c_612, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4'))) | ~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_608, c_54])).
% 2.91/1.39  tff(c_613, plain, (~r1_tarski(k1_zfmisc_1('#skF_3'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_612])).
% 2.91/1.39  tff(c_616, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_613])).
% 2.91/1.39  tff(c_620, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_616])).
% 2.91/1.39  tff(c_621, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1(k2_xboole_0('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_612])).
% 2.91/1.39  tff(c_625, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_621])).
% 2.91/1.39  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_156, c_625])).
% 2.91/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.39  
% 2.91/1.39  Inference rules
% 2.91/1.39  ----------------------
% 2.91/1.39  #Ref     : 0
% 2.91/1.39  #Sup     : 140
% 2.91/1.39  #Fact    : 0
% 2.91/1.39  #Define  : 0
% 2.91/1.39  #Split   : 1
% 2.91/1.39  #Chain   : 0
% 2.91/1.39  #Close   : 0
% 2.91/1.39  
% 2.91/1.39  Ordering : KBO
% 2.91/1.39  
% 2.91/1.39  Simplification rules
% 2.91/1.39  ----------------------
% 2.91/1.39  #Subsume      : 3
% 2.91/1.39  #Demod        : 87
% 2.91/1.39  #Tautology    : 42
% 2.91/1.39  #SimpNegUnit  : 0
% 2.91/1.39  #BackRed      : 0
% 2.91/1.39  
% 2.91/1.39  #Partial instantiations: 0
% 2.91/1.39  #Strategies tried      : 1
% 2.91/1.39  
% 2.91/1.39  Timing (in seconds)
% 2.91/1.39  ----------------------
% 2.91/1.40  Preprocessing        : 0.32
% 2.91/1.40  Parsing              : 0.17
% 2.91/1.40  CNF conversion       : 0.02
% 2.91/1.40  Main loop            : 0.32
% 2.91/1.40  Inferencing          : 0.12
% 2.91/1.40  Reduction            : 0.11
% 2.91/1.40  Demodulation         : 0.09
% 2.91/1.40  BG Simplification    : 0.02
% 2.91/1.40  Subsumption          : 0.05
% 2.91/1.40  Abstraction          : 0.02
% 2.91/1.40  MUC search           : 0.00
% 2.91/1.40  Cooper               : 0.00
% 2.91/1.40  Total                : 0.66
% 2.91/1.40  Index Insertion      : 0.00
% 2.91/1.40  Index Deletion       : 0.00
% 2.91/1.40  Index Matching       : 0.00
% 2.91/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
