%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:18 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 119 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 176 expanded)
%              Number of equality atoms :   29 (  87 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_6,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_28])).

tff(c_63,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_22,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_22])).

tff(c_71,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_63,c_63,c_32])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_20])).

tff(c_72,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k3_subset_1(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_72])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_80])).

tff(c_86,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_4,plain,(
    ! [A_3] : k1_subset_1(A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_subset_1(A_11)) = k2_subset_1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_subset_1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14])).

tff(c_35,plain,(
    ! [A_11] : k3_subset_1(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_30])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_111,plain,(
    ! [A_28,B_29] :
      ( k3_subset_1(A_28,k3_subset_1(A_28,B_29)) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_111])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k1_subset_1(A_12) = B_13
      | ~ r1_tarski(B_13,k3_subset_1(A_12,B_13))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_126,plain,(
    ! [B_30,A_31] :
      ( k1_xboole_0 = B_30
      | ~ r1_tarski(B_30,k3_subset_1(A_31,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_18])).

tff(c_129,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_126])).

tff(c_134,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_129])).

tff(c_136,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_184,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_10,c_136])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_184])).

tff(c_189,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_191,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_117])).

tff(c_195,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_191])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:08 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.28  
% 1.94/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.28  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.94/1.28  
% 1.94/1.28  %Foreground sorts:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Background operators:
% 1.94/1.28  
% 1.94/1.28  
% 1.94/1.28  %Foreground operators:
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.94/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.94/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.94/1.28  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.94/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.28  
% 1.94/1.29  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 1.94/1.29  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 1.94/1.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.94/1.29  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.94/1.29  tff(f_29, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.94/1.29  tff(f_45, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 1.94/1.29  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 1.94/1.29  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 1.94/1.29  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 1.94/1.29  tff(c_6, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.29  tff(c_28, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_31, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_28])).
% 1.94/1.29  tff(c_63, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_31])).
% 1.94/1.29  tff(c_22, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_32, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_22])).
% 1.94/1.29  tff(c_71, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_63, c_63, c_32])).
% 1.94/1.29  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.94/1.29  tff(c_64, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_20])).
% 1.94/1.29  tff(c_72, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k3_subset_1(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.29  tff(c_76, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_72])).
% 1.94/1.29  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.29  tff(c_80, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_76, c_2])).
% 1.94/1.29  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_80])).
% 1.94/1.29  tff(c_86, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_31])).
% 1.94/1.29  tff(c_4, plain, (![A_3]: (k1_subset_1(A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.29  tff(c_14, plain, (![A_11]: (k3_subset_1(A_11, k1_subset_1(A_11))=k2_subset_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.29  tff(c_30, plain, (![A_11]: (k3_subset_1(A_11, k1_subset_1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14])).
% 1.94/1.29  tff(c_35, plain, (![A_11]: (k3_subset_1(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_30])).
% 1.94/1.29  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.94/1.29  tff(c_85, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_31])).
% 1.94/1.29  tff(c_111, plain, (![A_28, B_29]: (k3_subset_1(A_28, k3_subset_1(A_28, B_29))=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.29  tff(c_117, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_111])).
% 1.94/1.29  tff(c_18, plain, (![A_12, B_13]: (k1_subset_1(A_12)=B_13 | ~r1_tarski(B_13, k3_subset_1(A_12, B_13)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.29  tff(c_126, plain, (![B_30, A_31]: (k1_xboole_0=B_30 | ~r1_tarski(B_30, k3_subset_1(A_31, B_30)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_18])).
% 1.94/1.29  tff(c_129, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_117, c_126])).
% 1.94/1.29  tff(c_134, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_129])).
% 1.94/1.29  tff(c_136, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_134])).
% 1.94/1.29  tff(c_184, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_136])).
% 1.94/1.29  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_184])).
% 1.94/1.29  tff(c_189, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_134])).
% 1.94/1.29  tff(c_191, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_117])).
% 1.94/1.29  tff(c_195, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_191])).
% 1.94/1.29  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_195])).
% 1.94/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  Inference rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Ref     : 0
% 1.94/1.29  #Sup     : 37
% 1.94/1.29  #Fact    : 0
% 1.94/1.29  #Define  : 0
% 1.94/1.29  #Split   : 2
% 1.94/1.29  #Chain   : 0
% 1.94/1.29  #Close   : 0
% 1.94/1.29  
% 1.94/1.29  Ordering : KBO
% 1.94/1.29  
% 1.94/1.29  Simplification rules
% 1.94/1.29  ----------------------
% 1.94/1.29  #Subsume      : 2
% 1.94/1.29  #Demod        : 26
% 1.94/1.29  #Tautology    : 25
% 1.94/1.29  #SimpNegUnit  : 2
% 1.94/1.29  #BackRed      : 5
% 1.94/1.29  
% 1.94/1.29  #Partial instantiations: 0
% 1.94/1.29  #Strategies tried      : 1
% 1.94/1.29  
% 1.94/1.29  Timing (in seconds)
% 1.94/1.29  ----------------------
% 1.94/1.29  Preprocessing        : 0.32
% 1.94/1.29  Parsing              : 0.17
% 1.94/1.29  CNF conversion       : 0.02
% 1.94/1.29  Main loop            : 0.15
% 1.94/1.29  Inferencing          : 0.05
% 1.94/1.29  Reduction            : 0.05
% 1.94/1.29  Demodulation         : 0.04
% 1.94/1.29  BG Simplification    : 0.01
% 1.94/1.29  Subsumption          : 0.02
% 1.94/1.29  Abstraction          : 0.01
% 1.94/1.29  MUC search           : 0.00
% 1.94/1.29  Cooper               : 0.00
% 1.94/1.29  Total                : 0.50
% 1.94/1.29  Index Insertion      : 0.00
% 1.94/1.29  Index Deletion       : 0.00
% 1.94/1.29  Index Matching       : 0.00
% 1.94/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
