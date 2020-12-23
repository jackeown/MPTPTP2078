%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 125 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 184 expanded)
%              Number of equality atoms :   30 (  88 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_16,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_74,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_32,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_42,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_82,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_42])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_30])).

tff(c_177,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_185,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_177])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_28,B_29,C_30] :
      ( r1_tarski(A_28,B_29)
      | ~ r1_tarski(A_28,k4_xboole_0(B_29,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [B_29,C_30] : r1_tarski(k4_xboole_0(B_29,C_30),B_29) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_210,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_104])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_210])).

tff(c_220,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_14,plain,(
    ! [A_8] : k1_subset_1(A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = k2_subset_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_subset_1(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_45,plain,(
    ! [A_16] : k3_subset_1(A_16,k1_xboole_0) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_219,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_403,plain,(
    ! [A_101,B_102] :
      ( k3_subset_1(A_101,k3_subset_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_409,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_403])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k1_subset_1(A_17) = B_18
      | ~ r1_tarski(B_18,k3_subset_1(A_17,B_18))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_425,plain,(
    ! [B_107,A_108] :
      ( k1_xboole_0 = B_107
      | ~ r1_tarski(B_107,k3_subset_1(A_108,B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_428,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_425])).

tff(c_433,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_428])).

tff(c_435,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_487,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_435])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_487])).

tff(c_492,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_496,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_409])).

tff(c_507,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_496])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:04:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.33  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.21/1.33  
% 2.21/1.33  %Foreground sorts:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Background operators:
% 2.21/1.33  
% 2.21/1.33  
% 2.21/1.33  %Foreground operators:
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.21/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.21/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.33  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.21/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.21/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.21/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.33  
% 2.54/1.34  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.54/1.34  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.54/1.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.54/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.54/1.34  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.54/1.34  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.54/1.34  tff(f_57, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.54/1.34  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.54/1.34  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.54/1.34  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.54/1.34  tff(c_16, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.54/1.34  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_41, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 2.54/1.34  tff(c_74, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_41])).
% 2.54/1.34  tff(c_32, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_42, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.54/1.34  tff(c_82, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_42])).
% 2.54/1.34  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.54/1.34  tff(c_75, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_30])).
% 2.54/1.34  tff(c_177, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.34  tff(c_185, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_75, c_177])).
% 2.54/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.54/1.34  tff(c_99, plain, (![A_28, B_29, C_30]: (r1_tarski(A_28, B_29) | ~r1_tarski(A_28, k4_xboole_0(B_29, C_30)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.54/1.34  tff(c_104, plain, (![B_29, C_30]: (r1_tarski(k4_xboole_0(B_29, C_30), B_29))), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.54/1.34  tff(c_210, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_185, c_104])).
% 2.54/1.34  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_210])).
% 2.54/1.34  tff(c_220, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_41])).
% 2.54/1.34  tff(c_14, plain, (![A_8]: (k1_subset_1(A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.34  tff(c_24, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=k2_subset_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.54/1.34  tff(c_40, plain, (![A_16]: (k3_subset_1(A_16, k1_subset_1(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.54/1.34  tff(c_45, plain, (![A_16]: (k3_subset_1(A_16, k1_xboole_0)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 2.54/1.34  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.34  tff(c_219, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_41])).
% 2.54/1.34  tff(c_403, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_subset_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.34  tff(c_409, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_403])).
% 2.54/1.34  tff(c_28, plain, (![A_17, B_18]: (k1_subset_1(A_17)=B_18 | ~r1_tarski(B_18, k3_subset_1(A_17, B_18)) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.54/1.34  tff(c_425, plain, (![B_107, A_108]: (k1_xboole_0=B_107 | ~r1_tarski(B_107, k3_subset_1(A_108, B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.54/1.34  tff(c_428, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_425])).
% 2.54/1.34  tff(c_433, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_219, c_428])).
% 2.54/1.34  tff(c_435, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_433])).
% 2.54/1.34  tff(c_487, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_435])).
% 2.54/1.34  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_487])).
% 2.54/1.34  tff(c_492, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_433])).
% 2.54/1.34  tff(c_496, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_409])).
% 2.54/1.34  tff(c_507, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_496])).
% 2.54/1.34  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_507])).
% 2.54/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.34  
% 2.54/1.34  Inference rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Ref     : 0
% 2.54/1.34  #Sup     : 104
% 2.54/1.34  #Fact    : 0
% 2.54/1.34  #Define  : 0
% 2.54/1.34  #Split   : 4
% 2.54/1.34  #Chain   : 0
% 2.54/1.34  #Close   : 0
% 2.54/1.34  
% 2.54/1.34  Ordering : KBO
% 2.54/1.34  
% 2.54/1.34  Simplification rules
% 2.54/1.34  ----------------------
% 2.54/1.34  #Subsume      : 3
% 2.54/1.34  #Demod        : 45
% 2.54/1.34  #Tautology    : 35
% 2.54/1.34  #SimpNegUnit  : 4
% 2.54/1.34  #BackRed      : 14
% 2.54/1.34  
% 2.54/1.34  #Partial instantiations: 0
% 2.54/1.34  #Strategies tried      : 1
% 2.54/1.34  
% 2.54/1.34  Timing (in seconds)
% 2.54/1.34  ----------------------
% 2.54/1.35  Preprocessing        : 0.31
% 2.54/1.35  Parsing              : 0.16
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.28
% 2.54/1.35  Inferencing          : 0.10
% 2.54/1.35  Reduction            : 0.09
% 2.54/1.35  Demodulation         : 0.06
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.06
% 2.54/1.35  Abstraction          : 0.02
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.62
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
