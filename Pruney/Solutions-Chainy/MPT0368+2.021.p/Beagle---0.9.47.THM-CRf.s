%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   53 (  58 expanded)
%              Number of leaves         :   25 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 102 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_67,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_xboole_0(A,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

tff(f_62,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_81,axiom,(
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

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_89,plain,(
    ! [B_43,A_44] :
      ( r2_hidden(B_43,A_44)
      | ~ m1_subset_1(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_10] : k3_tarski(k1_zfmisc_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,k3_tarski(B_38))
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_37,A_10] :
      ( r1_tarski(A_37,A_10)
      | ~ r2_hidden(A_37,k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_96,plain,(
    ! [B_43,A_10] :
      ( r1_tarski(B_43,A_10)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_89,c_82])).

tff(c_112,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(B_47,A_48)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_48)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_96])).

tff(c_124,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_112])).

tff(c_128,plain,(
    ! [A_50,C_51,B_52] :
      ( r2_xboole_0(A_50,C_51)
      | ~ r1_tarski(B_52,C_51)
      | ~ r2_xboole_0(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,(
    ! [A_53] :
      ( r2_xboole_0(A_53,'#skF_2')
      | ~ r2_xboole_0(A_53,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_124,c_128])).

tff(c_8,plain,(
    ! [A_3] : ~ r2_xboole_0(A_3,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ~ r2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_150,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_147])).

tff(c_153,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_150])).

tff(c_24,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k2_subset_1(A_14),k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    ! [A_14] : m1_subset_1(A_14,k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_34,plain,(
    ! [A_16,B_17,C_21] :
      ( m1_subset_1('#skF_1'(A_16,B_17,C_21),A_16)
      | r1_tarski(B_17,C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_38,plain,(
    ! [C_24] :
      ( r2_hidden(C_24,'#skF_3')
      | ~ m1_subset_1(C_24,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_318,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r2_hidden('#skF_1'(A_91,B_92,C_93),C_93)
      | r1_tarski(B_92,C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_394,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_102))
      | ~ m1_subset_1('#skF_1'(A_102,B_101,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_318])).

tff(c_398,plain,(
    ! [B_17] :
      ( r1_tarski(B_17,'#skF_3')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_394])).

tff(c_406,plain,(
    ! [B_103] :
      ( r1_tarski(B_103,'#skF_3')
      | ~ m1_subset_1(B_103,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_398])).

tff(c_421,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_41,c_406])).

tff(c_429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_421])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  
% 2.63/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.37  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 2.63/1.37  
% 2.63/1.37  %Foreground sorts:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Background operators:
% 2.63/1.37  
% 2.63/1.37  
% 2.63/1.37  %Foreground operators:
% 2.63/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.37  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.63/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.37  
% 2.63/1.38  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 2.63/1.38  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.63/1.38  tff(f_67, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.63/1.38  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.38  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.63/1.38  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.63/1.38  tff(f_41, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.63/1.38  tff(f_35, axiom, (![A, B]: ~r2_xboole_0(A, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', irreflexivity_r2_xboole_0)).
% 2.63/1.38  tff(f_62, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.63/1.38  tff(f_64, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.63/1.38  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.63/1.38  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.38  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.63/1.38  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.38  tff(c_28, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.63/1.38  tff(c_89, plain, (![B_43, A_44]: (r2_hidden(B_43, A_44) | ~m1_subset_1(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.63/1.38  tff(c_14, plain, (![A_10]: (k3_tarski(k1_zfmisc_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.63/1.38  tff(c_79, plain, (![A_37, B_38]: (r1_tarski(A_37, k3_tarski(B_38)) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.63/1.38  tff(c_82, plain, (![A_37, A_10]: (r1_tarski(A_37, A_10) | ~r2_hidden(A_37, k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_79])).
% 2.63/1.38  tff(c_96, plain, (![B_43, A_10]: (r1_tarski(B_43, A_10) | ~m1_subset_1(B_43, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_89, c_82])).
% 2.63/1.38  tff(c_112, plain, (![B_47, A_48]: (r1_tarski(B_47, A_48) | ~m1_subset_1(B_47, k1_zfmisc_1(A_48)))), inference(negUnitSimplification, [status(thm)], [c_28, c_96])).
% 2.63/1.38  tff(c_124, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_112])).
% 2.63/1.38  tff(c_128, plain, (![A_50, C_51, B_52]: (r2_xboole_0(A_50, C_51) | ~r1_tarski(B_52, C_51) | ~r2_xboole_0(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.63/1.38  tff(c_138, plain, (![A_53]: (r2_xboole_0(A_53, '#skF_2') | ~r2_xboole_0(A_53, '#skF_3'))), inference(resolution, [status(thm)], [c_124, c_128])).
% 2.63/1.38  tff(c_8, plain, (![A_3]: (~r2_xboole_0(A_3, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.38  tff(c_147, plain, (~r2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.63/1.38  tff(c_150, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2, c_147])).
% 2.63/1.38  tff(c_153, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_150])).
% 2.63/1.38  tff(c_24, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.63/1.38  tff(c_26, plain, (![A_14]: (m1_subset_1(k2_subset_1(A_14), k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.63/1.38  tff(c_41, plain, (![A_14]: (m1_subset_1(A_14, k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.63/1.38  tff(c_34, plain, (![A_16, B_17, C_21]: (m1_subset_1('#skF_1'(A_16, B_17, C_21), A_16) | r1_tarski(B_17, C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.63/1.38  tff(c_38, plain, (![C_24]: (r2_hidden(C_24, '#skF_3') | ~m1_subset_1(C_24, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.63/1.38  tff(c_318, plain, (![A_91, B_92, C_93]: (~r2_hidden('#skF_1'(A_91, B_92, C_93), C_93) | r1_tarski(B_92, C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.63/1.38  tff(c_394, plain, (![B_101, A_102]: (r1_tarski(B_101, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_102)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_102)) | ~m1_subset_1('#skF_1'(A_102, B_101, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_318])).
% 2.63/1.38  tff(c_398, plain, (![B_17]: (r1_tarski(B_17, '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_17, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_34, c_394])).
% 2.63/1.38  tff(c_406, plain, (![B_103]: (r1_tarski(B_103, '#skF_3') | ~m1_subset_1(B_103, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_398])).
% 2.63/1.38  tff(c_421, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_41, c_406])).
% 2.63/1.38  tff(c_429, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_421])).
% 2.63/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  Inference rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Ref     : 0
% 2.63/1.38  #Sup     : 80
% 2.63/1.38  #Fact    : 0
% 2.63/1.38  #Define  : 0
% 2.63/1.38  #Split   : 3
% 2.63/1.38  #Chain   : 0
% 2.63/1.38  #Close   : 0
% 2.63/1.38  
% 2.63/1.38  Ordering : KBO
% 2.63/1.38  
% 2.63/1.38  Simplification rules
% 2.63/1.38  ----------------------
% 2.63/1.38  #Subsume      : 16
% 2.63/1.38  #Demod        : 5
% 2.63/1.38  #Tautology    : 12
% 2.63/1.38  #SimpNegUnit  : 11
% 2.63/1.38  #BackRed      : 0
% 2.63/1.38  
% 2.63/1.38  #Partial instantiations: 0
% 2.63/1.38  #Strategies tried      : 1
% 2.63/1.38  
% 2.63/1.38  Timing (in seconds)
% 2.63/1.38  ----------------------
% 2.63/1.39  Preprocessing        : 0.32
% 2.63/1.39  Parsing              : 0.17
% 2.63/1.39  CNF conversion       : 0.02
% 2.63/1.39  Main loop            : 0.28
% 2.63/1.39  Inferencing          : 0.10
% 2.63/1.39  Reduction            : 0.07
% 2.63/1.39  Demodulation         : 0.05
% 2.63/1.39  BG Simplification    : 0.02
% 2.63/1.39  Subsumption          : 0.08
% 2.63/1.39  Abstraction          : 0.01
% 2.63/1.39  MUC search           : 0.00
% 2.63/1.39  Cooper               : 0.00
% 2.63/1.39  Total                : 0.64
% 2.63/1.39  Index Insertion      : 0.00
% 2.63/1.39  Index Deletion       : 0.00
% 2.63/1.39  Index Matching       : 0.00
% 2.63/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
