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
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 134 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 192 expanded)
%              Number of equality atoms :   29 (  98 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : k1_subset_1(A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = k2_subset_1(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8] :
      ( r1_tarski(k1_subset_1(A_8),k3_subset_1(A_8,k1_subset_1(A_8)))
      | ~ m1_subset_1(k1_subset_1(A_8),k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_27,plain,(
    ! [A_8] :
      ( r1_tarski(k1_subset_1(A_8),k2_subset_1(A_8))
      | ~ m1_subset_1(k1_subset_1(A_8),k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_31,plain,(
    ! [A_8] :
      ( r1_tarski(k1_subset_1(A_8),A_8)
      | ~ m1_subset_1(k1_subset_1(A_8),k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_27])).

tff(c_32,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_31])).

tff(c_36,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_28,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_subset_1(A_7)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_34,plain,(
    ! [A_7] : k3_subset_1(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_80,plain,(
    ! [A_19,B_20] :
      ( k3_subset_1(A_19,k3_subset_1(A_19,B_20)) = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [A_10] : k3_subset_1(A_10,k3_subset_1(A_10,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_90,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_86])).

tff(c_26,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_64,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_29,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20])).

tff(c_71,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_29])).

tff(c_91,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_71])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_91])).

tff(c_96,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k3_subset_1(A_3,B_4),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_106,plain,(
    ! [A_24,B_25] :
      ( k3_subset_1(A_24,k3_subset_1(A_24,B_25)) = B_25
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k1_subset_1(A_8) = B_9
      | ~ r1_tarski(B_9,k3_subset_1(A_8,B_9))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_27,A_28] :
      ( k1_xboole_0 = B_27
      | ~ r1_tarski(B_27,k3_subset_1(A_28,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14])).

tff(c_154,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_151])).

tff(c_166,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_154])).

tff(c_234,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_237,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_234])).

tff(c_241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_237])).

tff(c_242,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_244,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_117])).

tff(c_246,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_244])).

tff(c_248,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  %$ r1_tarski > m1_subset_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.22  
% 1.94/1.22  %Foreground sorts:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Background operators:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Foreground operators:
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.94/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.22  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.94/1.22  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.94/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.22  
% 1.94/1.23  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.94/1.23  tff(f_27, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.94/1.23  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.94/1.23  tff(f_39, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 1.94/1.23  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 1.94/1.23  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.94/1.23  tff(f_54, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 1.94/1.23  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.94/1.23  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.23  tff(c_2, plain, (![A_1]: (k1_subset_1(A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.23  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.23  tff(c_10, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=k2_subset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.23  tff(c_12, plain, (![A_8]: (r1_tarski(k1_subset_1(A_8), k3_subset_1(A_8, k1_subset_1(A_8))) | ~m1_subset_1(k1_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.23  tff(c_27, plain, (![A_8]: (r1_tarski(k1_subset_1(A_8), k2_subset_1(A_8)) | ~m1_subset_1(k1_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 1.94/1.23  tff(c_31, plain, (![A_8]: (r1_tarski(k1_subset_1(A_8), A_8) | ~m1_subset_1(k1_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_27])).
% 1.94/1.23  tff(c_32, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_31])).
% 1.94/1.23  tff(c_36, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 1.94/1.23  tff(c_28, plain, (![A_7]: (k3_subset_1(A_7, k1_subset_1(A_7))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_10])).
% 1.94/1.23  tff(c_34, plain, (![A_7]: (k3_subset_1(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 1.94/1.23  tff(c_80, plain, (![A_19, B_20]: (k3_subset_1(A_19, k3_subset_1(A_19, B_20))=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.23  tff(c_86, plain, (![A_10]: (k3_subset_1(A_10, k3_subset_1(A_10, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_80])).
% 1.94/1.23  tff(c_90, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_86])).
% 1.94/1.23  tff(c_26, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.23  tff(c_30, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 1.94/1.23  tff(c_64, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_30])).
% 1.94/1.23  tff(c_20, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.23  tff(c_29, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20])).
% 1.94/1.23  tff(c_71, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_29])).
% 1.94/1.23  tff(c_91, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_71])).
% 1.94/1.23  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_91])).
% 1.94/1.23  tff(c_96, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 1.94/1.23  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.94/1.23  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(k3_subset_1(A_3, B_4), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.23  tff(c_95, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 1.94/1.23  tff(c_106, plain, (![A_24, B_25]: (k3_subset_1(A_24, k3_subset_1(A_24, B_25))=B_25 | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.23  tff(c_117, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_106])).
% 1.94/1.23  tff(c_14, plain, (![A_8, B_9]: (k1_subset_1(A_8)=B_9 | ~r1_tarski(B_9, k3_subset_1(A_8, B_9)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.23  tff(c_151, plain, (![B_27, A_28]: (k1_xboole_0=B_27 | ~r1_tarski(B_27, k3_subset_1(A_28, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14])).
% 1.94/1.23  tff(c_154, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_151])).
% 1.94/1.23  tff(c_166, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_154])).
% 1.94/1.23  tff(c_234, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_166])).
% 1.94/1.23  tff(c_237, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_234])).
% 1.94/1.23  tff(c_241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_237])).
% 1.94/1.23  tff(c_242, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_166])).
% 1.94/1.23  tff(c_244, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_117])).
% 1.94/1.23  tff(c_246, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_244])).
% 1.94/1.23  tff(c_248, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_246])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 43
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 2
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 2
% 1.94/1.23  #Demod        : 45
% 1.94/1.23  #Tautology    : 33
% 1.94/1.23  #SimpNegUnit  : 1
% 1.94/1.23  #BackRed      : 4
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.24  ----------------------
% 1.94/1.24  Preprocessing        : 0.26
% 1.94/1.24  Parsing              : 0.14
% 1.94/1.24  CNF conversion       : 0.02
% 1.94/1.24  Main loop            : 0.19
% 1.94/1.24  Inferencing          : 0.06
% 1.94/1.24  Reduction            : 0.07
% 1.94/1.24  Demodulation         : 0.06
% 1.94/1.24  BG Simplification    : 0.01
% 1.94/1.24  Subsumption          : 0.03
% 1.94/1.24  Abstraction          : 0.01
% 1.94/1.24  MUC search           : 0.00
% 1.94/1.24  Cooper               : 0.00
% 1.94/1.24  Total                : 0.48
% 1.94/1.24  Index Insertion      : 0.00
% 1.94/1.24  Index Deletion       : 0.00
% 1.94/1.24  Index Matching       : 0.00
% 1.94/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
