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
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 122 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 184 expanded)
%              Number of equality atoms :   22 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_52,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_18,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k2_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_189,plain,(
    ! [C_56,A_57,B_58] :
      ( r2_hidden(C_56,A_57)
      | ~ r2_hidden(C_56,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_213,plain,(
    ! [A_64,B_65,A_66] :
      ( r2_hidden('#skF_1'(A_64,B_65),A_66)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(A_66))
      | r1_tarski(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_189])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_225,plain,(
    ! [A_67,A_68] :
      ( ~ m1_subset_1(A_67,k1_zfmisc_1(A_68))
      | r1_tarski(A_67,A_68) ) ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_235,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k3_subset_1(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(resolution,[status(thm)],[c_24,c_225])).

tff(c_44,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | k2_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_47,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_44])).

tff(c_72,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_38,plain,
    ( k2_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,
    ( '#skF_2' != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_38])).

tff(c_94,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_72,c_50])).

tff(c_240,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_235,c_94])).

tff(c_254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_240])).

tff(c_256,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_255,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_257,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_257])).

tff(c_261,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_394,plain,(
    ! [A_96,B_97] :
      ( k3_subset_1(A_96,k3_subset_1(A_96,B_97)) = B_97
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_402,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_394])).

tff(c_456,plain,(
    ! [A_102,B_103] :
      ( k1_subset_1(A_102) = B_103
      | ~ r1_tarski(B_103,k3_subset_1(A_102,B_103))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_465,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_456])).

tff(c_472,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_465])).

tff(c_474,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_477,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_474])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_477])).

tff(c_482,plain,(
    k3_subset_1('#skF_2','#skF_3') = k1_subset_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_498,plain,(
    k3_subset_1('#skF_2',k1_subset_1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_402])).

tff(c_30,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = k2_subset_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_534,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_48])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_534])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:36:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  
% 2.29/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.33  
% 2.29/1.33  %Foreground sorts:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Background operators:
% 2.29/1.33  
% 2.29/1.33  
% 2.29/1.33  %Foreground operators:
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.29/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.29/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.29/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.29/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.33  
% 2.29/1.34  tff(f_46, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.29/1.34  tff(f_52, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.29/1.34  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.29/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.29/1.34  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.29/1.34  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.29/1.34  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.29/1.34  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.29/1.34  tff(f_69, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.29/1.34  tff(c_18, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.29/1.34  tff(c_22, plain, (![A_15]: (m1_subset_1(k2_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.29/1.34  tff(c_46, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 2.29/1.34  tff(c_24, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.29/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.34  tff(c_189, plain, (![C_56, A_57, B_58]: (r2_hidden(C_56, A_57) | ~r2_hidden(C_56, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.29/1.34  tff(c_213, plain, (![A_64, B_65, A_66]: (r2_hidden('#skF_1'(A_64, B_65), A_66) | ~m1_subset_1(A_64, k1_zfmisc_1(A_66)) | r1_tarski(A_64, B_65))), inference(resolution, [status(thm)], [c_6, c_189])).
% 2.29/1.34  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.29/1.34  tff(c_225, plain, (![A_67, A_68]: (~m1_subset_1(A_67, k1_zfmisc_1(A_68)) | r1_tarski(A_67, A_68))), inference(resolution, [status(thm)], [c_213, c_4])).
% 2.29/1.34  tff(c_235, plain, (![A_69, B_70]: (r1_tarski(k3_subset_1(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(resolution, [status(thm)], [c_24, c_225])).
% 2.29/1.34  tff(c_44, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | k2_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.34  tff(c_47, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_44])).
% 2.29/1.34  tff(c_72, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_47])).
% 2.29/1.34  tff(c_38, plain, (k2_subset_1('#skF_2')!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.34  tff(c_50, plain, ('#skF_2'!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_38])).
% 2.29/1.34  tff(c_94, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_72, c_50])).
% 2.29/1.34  tff(c_240, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_235, c_94])).
% 2.29/1.34  tff(c_254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_240])).
% 2.29/1.34  tff(c_256, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_47])).
% 2.29/1.34  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.29/1.34  tff(c_255, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_47])).
% 2.29/1.34  tff(c_257, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 2.29/1.34  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_255, c_257])).
% 2.29/1.34  tff(c_261, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 2.29/1.34  tff(c_394, plain, (![A_96, B_97]: (k3_subset_1(A_96, k3_subset_1(A_96, B_97))=B_97 | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.29/1.34  tff(c_402, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_394])).
% 2.29/1.34  tff(c_456, plain, (![A_102, B_103]: (k1_subset_1(A_102)=B_103 | ~r1_tarski(B_103, k3_subset_1(A_102, B_103)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.29/1.34  tff(c_465, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_402, c_456])).
% 2.29/1.34  tff(c_472, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_465])).
% 2.29/1.34  tff(c_474, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_472])).
% 2.29/1.34  tff(c_477, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_474])).
% 2.29/1.34  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_477])).
% 2.29/1.34  tff(c_482, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_subset_1('#skF_2')), inference(splitRight, [status(thm)], [c_472])).
% 2.29/1.34  tff(c_498, plain, (k3_subset_1('#skF_2', k1_subset_1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_482, c_402])).
% 2.29/1.34  tff(c_30, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=k2_subset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.29/1.34  tff(c_48, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 2.29/1.34  tff(c_534, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_498, c_48])).
% 2.29/1.34  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_534])).
% 2.29/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.34  
% 2.29/1.34  Inference rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Ref     : 0
% 2.29/1.34  #Sup     : 116
% 2.29/1.34  #Fact    : 0
% 2.29/1.34  #Define  : 0
% 2.29/1.34  #Split   : 4
% 2.29/1.34  #Chain   : 0
% 2.29/1.34  #Close   : 0
% 2.29/1.34  
% 2.29/1.34  Ordering : KBO
% 2.29/1.34  
% 2.29/1.34  Simplification rules
% 2.29/1.34  ----------------------
% 2.29/1.34  #Subsume      : 2
% 2.29/1.34  #Demod        : 48
% 2.29/1.34  #Tautology    : 64
% 2.29/1.34  #SimpNegUnit  : 1
% 2.29/1.34  #BackRed      : 11
% 2.29/1.34  
% 2.29/1.34  #Partial instantiations: 0
% 2.29/1.34  #Strategies tried      : 1
% 2.29/1.34  
% 2.29/1.34  Timing (in seconds)
% 2.29/1.34  ----------------------
% 2.60/1.34  Preprocessing        : 0.31
% 2.60/1.34  Parsing              : 0.16
% 2.60/1.34  CNF conversion       : 0.02
% 2.60/1.35  Main loop            : 0.28
% 2.60/1.35  Inferencing          : 0.10
% 2.60/1.35  Reduction            : 0.09
% 2.60/1.35  Demodulation         : 0.06
% 2.60/1.35  BG Simplification    : 0.02
% 2.60/1.35  Subsumption          : 0.06
% 2.60/1.35  Abstraction          : 0.02
% 2.60/1.35  MUC search           : 0.00
% 2.60/1.35  Cooper               : 0.00
% 2.60/1.35  Total                : 0.62
% 2.60/1.35  Index Insertion      : 0.00
% 2.60/1.35  Index Deletion       : 0.00
% 2.60/1.35  Index Matching       : 0.00
% 2.60/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
