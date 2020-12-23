%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:49 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 (  91 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_57,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_37,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_95,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_70,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_28,A_5] :
      ( r1_tarski(A_28,A_5)
      | ~ r2_hidden(A_28,k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_102,plain,(
    ! [B_38,A_5] :
      ( r1_tarski(B_38,A_5)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_95,c_73])).

tff(c_112,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(B_43,A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_102])).

tff(c_129,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_112])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_136,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_133])).

tff(c_20,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_30,plain,(
    ! [A_11,B_12,C_16] :
      ( m1_subset_1('#skF_1'(A_11,B_12,C_16),A_11)
      | r1_tarski(B_12,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    ! [C_19] :
      ( r2_hidden(C_19,'#skF_3')
      | ~ m1_subset_1(C_19,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_197,plain,(
    ! [A_53,B_54,C_55] :
      ( ~ r2_hidden('#skF_1'(A_53,B_54,C_55),C_55)
      | r1_tarski(B_54,C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_352,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ m1_subset_1('#skF_1'(A_75,B_74,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_197])).

tff(c_356,plain,(
    ! [B_12] :
      ( r1_tarski(B_12,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_12,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_364,plain,(
    ! [B_76] :
      ( r1_tarski(B_76,'#skF_3')
      | ~ m1_subset_1(B_76,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_356])).

tff(c_379,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_364])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_136,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:18:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  
% 2.28/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.30  
% 2.28/1.30  %Foreground sorts:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Background operators:
% 2.28/1.30  
% 2.28/1.30  
% 2.28/1.30  %Foreground operators:
% 2.28/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.28/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.30  
% 2.53/1.31  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.53/1.31  tff(f_57, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.53/1.31  tff(f_50, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.53/1.31  tff(f_37, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.53/1.31  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.53/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.53/1.31  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.53/1.31  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.53/1.31  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.53/1.31  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.31  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.31  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.53/1.31  tff(c_95, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.53/1.31  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.53/1.31  tff(c_70, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.53/1.31  tff(c_73, plain, (![A_28, A_5]: (r1_tarski(A_28, A_5) | ~r2_hidden(A_28, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 2.53/1.31  tff(c_102, plain, (![B_38, A_5]: (r1_tarski(B_38, A_5) | ~m1_subset_1(B_38, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_95, c_73])).
% 2.53/1.31  tff(c_112, plain, (![B_43, A_44]: (r1_tarski(B_43, A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)))), inference(negUnitSimplification, [status(thm)], [c_24, c_102])).
% 2.53/1.31  tff(c_129, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_112])).
% 2.53/1.31  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.31  tff(c_133, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_129, c_2])).
% 2.53/1.31  tff(c_136, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_133])).
% 2.53/1.31  tff(c_20, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.31  tff(c_22, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.53/1.31  tff(c_37, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 2.53/1.31  tff(c_30, plain, (![A_11, B_12, C_16]: (m1_subset_1('#skF_1'(A_11, B_12, C_16), A_11) | r1_tarski(B_12, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.31  tff(c_34, plain, (![C_19]: (r2_hidden(C_19, '#skF_3') | ~m1_subset_1(C_19, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.53/1.31  tff(c_197, plain, (![A_53, B_54, C_55]: (~r2_hidden('#skF_1'(A_53, B_54, C_55), C_55) | r1_tarski(B_54, C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.53/1.31  tff(c_352, plain, (![B_74, A_75]: (r1_tarski(B_74, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_75)) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~m1_subset_1('#skF_1'(A_75, B_74, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_197])).
% 2.53/1.31  tff(c_356, plain, (![B_12]: (r1_tarski(B_12, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_12, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_30, c_352])).
% 2.53/1.31  tff(c_364, plain, (![B_76]: (r1_tarski(B_76, '#skF_3') | ~m1_subset_1(B_76, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_356])).
% 2.53/1.31  tff(c_379, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_37, c_364])).
% 2.53/1.31  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_136, c_379])).
% 2.53/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.31  
% 2.53/1.31  Inference rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Ref     : 0
% 2.53/1.31  #Sup     : 65
% 2.53/1.31  #Fact    : 0
% 2.53/1.31  #Define  : 0
% 2.53/1.31  #Split   : 2
% 2.53/1.31  #Chain   : 0
% 2.53/1.31  #Close   : 0
% 2.53/1.31  
% 2.53/1.31  Ordering : KBO
% 2.53/1.31  
% 2.53/1.31  Simplification rules
% 2.53/1.31  ----------------------
% 2.53/1.31  #Subsume      : 13
% 2.53/1.31  #Demod        : 15
% 2.53/1.31  #Tautology    : 17
% 2.53/1.31  #SimpNegUnit  : 11
% 2.53/1.31  #BackRed      : 0
% 2.53/1.31  
% 2.53/1.31  #Partial instantiations: 0
% 2.53/1.31  #Strategies tried      : 1
% 2.53/1.31  
% 2.53/1.31  Timing (in seconds)
% 2.53/1.31  ----------------------
% 2.53/1.31  Preprocessing        : 0.30
% 2.53/1.31  Parsing              : 0.16
% 2.53/1.31  CNF conversion       : 0.02
% 2.53/1.31  Main loop            : 0.26
% 2.53/1.31  Inferencing          : 0.09
% 2.53/1.31  Reduction            : 0.07
% 2.53/1.31  Demodulation         : 0.05
% 2.53/1.31  BG Simplification    : 0.01
% 2.53/1.31  Subsumption          : 0.07
% 2.53/1.31  Abstraction          : 0.01
% 2.53/1.31  MUC search           : 0.00
% 2.53/1.31  Cooper               : 0.00
% 2.53/1.31  Total                : 0.59
% 2.53/1.31  Index Insertion      : 0.00
% 2.53/1.31  Index Deletion       : 0.00
% 2.53/1.31  Index Matching       : 0.00
% 2.53/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
