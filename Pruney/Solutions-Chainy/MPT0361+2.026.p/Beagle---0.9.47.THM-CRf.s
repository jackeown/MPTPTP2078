%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  65 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 (  91 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_156,plain,(
    ! [A_82,B_83,C_84] :
      ( k4_subset_1(A_82,B_83,C_84) = k2_xboole_0(B_83,C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,(
    ! [B_85] :
      ( k4_subset_1('#skF_3',B_85,'#skF_5') = k2_xboole_0(B_85,'#skF_5')
      | ~ m1_subset_1(B_85,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_48,c_156])).

tff(c_171,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_163])).

tff(c_181,plain,(
    ! [A_86,B_87,C_88] :
      ( m1_subset_1(k4_subset_1(A_86,B_87,C_88),k1_zfmisc_1(A_86))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_190,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_181])).

tff(c_197,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_190])).

tff(c_63,plain,(
    ! [A_48,B_49] : k1_enumset1(A_48,A_48,B_49) = k2_tarski(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_72,plain,(
    ! [A_48,B_49] : r2_hidden(A_48,k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_6])).

tff(c_36,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_84,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,k3_tarski(B_55))
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_97,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(A_59,k2_xboole_0(A_60,B_61))
      | ~ r2_hidden(A_59,k2_tarski(A_60,B_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_84])).

tff(c_104,plain,(
    ! [A_48,B_49] : r1_tarski(A_48,k2_xboole_0(A_48,B_49)) ),
    inference(resolution,[status(thm)],[c_72,c_97])).

tff(c_785,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(k3_subset_1(A_105,C_106),k3_subset_1(A_105,B_107))
      | ~ r1_tarski(B_107,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_176,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_46])).

tff(c_788,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_785,c_176])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_197,c_104,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.52  
% 3.06/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.17/1.52  
% 3.17/1.52  %Foreground sorts:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Background operators:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Foreground operators:
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.52  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.17/1.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.17/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.17/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.52  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.17/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.17/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.52  
% 3.19/1.53  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 3.19/1.53  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.19/1.53  tff(f_60, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 3.19/1.53  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.19/1.53  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.19/1.53  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.19/1.53  tff(f_52, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.19/1.53  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.19/1.53  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.53  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.53  tff(c_156, plain, (![A_82, B_83, C_84]: (k4_subset_1(A_82, B_83, C_84)=k2_xboole_0(B_83, C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.53  tff(c_163, plain, (![B_85]: (k4_subset_1('#skF_3', B_85, '#skF_5')=k2_xboole_0(B_85, '#skF_5') | ~m1_subset_1(B_85, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_156])).
% 3.19/1.53  tff(c_171, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_163])).
% 3.19/1.53  tff(c_181, plain, (![A_86, B_87, C_88]: (m1_subset_1(k4_subset_1(A_86, B_87, C_88), k1_zfmisc_1(A_86)) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.53  tff(c_190, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_171, c_181])).
% 3.19/1.53  tff(c_197, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_190])).
% 3.19/1.53  tff(c_63, plain, (![A_48, B_49]: (k1_enumset1(A_48, A_48, B_49)=k2_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.53  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.19/1.53  tff(c_72, plain, (![A_48, B_49]: (r2_hidden(A_48, k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_6])).
% 3.19/1.53  tff(c_36, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.19/1.53  tff(c_84, plain, (![A_54, B_55]: (r1_tarski(A_54, k3_tarski(B_55)) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.19/1.53  tff(c_97, plain, (![A_59, A_60, B_61]: (r1_tarski(A_59, k2_xboole_0(A_60, B_61)) | ~r2_hidden(A_59, k2_tarski(A_60, B_61)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_84])).
% 3.19/1.53  tff(c_104, plain, (![A_48, B_49]: (r1_tarski(A_48, k2_xboole_0(A_48, B_49)))), inference(resolution, [status(thm)], [c_72, c_97])).
% 3.19/1.53  tff(c_785, plain, (![A_105, C_106, B_107]: (r1_tarski(k3_subset_1(A_105, C_106), k3_subset_1(A_105, B_107)) | ~r1_tarski(B_107, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.19/1.53  tff(c_46, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.53  tff(c_176, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_46])).
% 3.19/1.53  tff(c_788, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_785, c_176])).
% 3.19/1.53  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_197, c_104, c_788])).
% 3.19/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.53  
% 3.19/1.53  Inference rules
% 3.19/1.53  ----------------------
% 3.19/1.53  #Ref     : 0
% 3.19/1.53  #Sup     : 194
% 3.19/1.53  #Fact    : 0
% 3.19/1.53  #Define  : 0
% 3.19/1.53  #Split   : 0
% 3.19/1.53  #Chain   : 0
% 3.19/1.53  #Close   : 0
% 3.19/1.53  
% 3.19/1.53  Ordering : KBO
% 3.19/1.53  
% 3.19/1.53  Simplification rules
% 3.19/1.53  ----------------------
% 3.19/1.53  #Subsume      : 0
% 3.19/1.53  #Demod        : 39
% 3.19/1.53  #Tautology    : 50
% 3.19/1.53  #SimpNegUnit  : 0
% 3.19/1.53  #BackRed      : 1
% 3.19/1.53  
% 3.19/1.53  #Partial instantiations: 0
% 3.19/1.53  #Strategies tried      : 1
% 3.19/1.53  
% 3.19/1.53  Timing (in seconds)
% 3.19/1.53  ----------------------
% 3.19/1.54  Preprocessing        : 0.35
% 3.19/1.54  Parsing              : 0.18
% 3.19/1.54  CNF conversion       : 0.03
% 3.19/1.54  Main loop            : 0.36
% 3.19/1.54  Inferencing          : 0.12
% 3.19/1.54  Reduction            : 0.11
% 3.19/1.54  Demodulation         : 0.08
% 3.19/1.54  BG Simplification    : 0.02
% 3.19/1.54  Subsumption          : 0.08
% 3.19/1.54  Abstraction          : 0.03
% 3.19/1.54  MUC search           : 0.00
% 3.19/1.54  Cooper               : 0.00
% 3.19/1.54  Total                : 0.74
% 3.19/1.54  Index Insertion      : 0.00
% 3.19/1.54  Index Deletion       : 0.00
% 3.19/1.54  Index Matching       : 0.00
% 3.19/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
