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
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 144 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 217 expanded)
%              Number of equality atoms :   39 ( 109 expanded)
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

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_12,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_106,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_94])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_16,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_77,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_82,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_41])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_84,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_30])).

tff(c_209,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_209])).

tff(c_218,plain,(
    k3_subset_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_215])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_93,plain,(
    k4_xboole_0(k3_subset_1('#skF_1','#skF_1'),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_82,c_81])).

tff(c_220,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_93])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_220])).

tff(c_226,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = k2_subset_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_45,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k3_subset_1(A_10,B_11),k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_363,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_369,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_363])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( k1_subset_1(A_15) = B_16
      | ~ r1_tarski(B_16,k3_subset_1(A_15,B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_395,plain,(
    ! [B_60,A_61] :
      ( k1_xboole_0 = B_60
      | ~ r1_tarski(B_60,k3_subset_1(A_61,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_398,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_395])).

tff(c_411,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_398])).

tff(c_418,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_411])).

tff(c_421,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_421])).

tff(c_426,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_411])).

tff(c_428,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_369])).

tff(c_434,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_428])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:46:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.10/1.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.10/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.26  
% 2.10/1.27  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.10/1.27  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.10/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.10/1.27  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.10/1.27  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.10/1.27  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.10/1.27  tff(f_39, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.10/1.27  tff(f_55, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.10/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.10/1.27  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.10/1.27  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.10/1.27  tff(c_12, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.27  tff(c_94, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.27  tff(c_106, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_94])).
% 2.10/1.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_105, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_94])).
% 2.10/1.27  tff(c_16, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.27  tff(c_32, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_42, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.10/1.27  tff(c_77, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.10/1.27  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_41, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 2.10/1.27  tff(c_82, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_41])).
% 2.10/1.27  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.10/1.27  tff(c_84, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_30])).
% 2.10/1.27  tff(c_209, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.27  tff(c_215, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_209])).
% 2.10/1.27  tff(c_218, plain, (k3_subset_1('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_215])).
% 2.10/1.27  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.27  tff(c_81, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_77])).
% 2.10/1.27  tff(c_93, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_82, c_82, c_81])).
% 2.10/1.27  tff(c_220, plain, (k4_xboole_0(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_93])).
% 2.10/1.27  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_220])).
% 2.10/1.27  tff(c_226, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 2.10/1.27  tff(c_14, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.27  tff(c_24, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=k2_subset_1(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.27  tff(c_40, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.10/1.27  tff(c_45, plain, (![A_14]: (k3_subset_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 2.10/1.27  tff(c_20, plain, (![A_10, B_11]: (m1_subset_1(k3_subset_1(A_10, B_11), k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.27  tff(c_227, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.10/1.27  tff(c_363, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.27  tff(c_369, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_363])).
% 2.10/1.27  tff(c_28, plain, (![A_15, B_16]: (k1_subset_1(A_15)=B_16 | ~r1_tarski(B_16, k3_subset_1(A_15, B_16)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.27  tff(c_395, plain, (![B_60, A_61]: (k1_xboole_0=B_60 | ~r1_tarski(B_60, k3_subset_1(A_61, B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.10/1.27  tff(c_398, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_369, c_395])).
% 2.10/1.27  tff(c_411, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_398])).
% 2.10/1.27  tff(c_418, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_411])).
% 2.10/1.27  tff(c_421, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_418])).
% 2.10/1.27  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_421])).
% 2.10/1.27  tff(c_426, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_411])).
% 2.10/1.27  tff(c_428, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_369])).
% 2.10/1.27  tff(c_434, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_428])).
% 2.10/1.27  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_434])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 83
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 4
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 6
% 2.10/1.27  #Demod        : 40
% 2.10/1.27  #Tautology    : 53
% 2.10/1.27  #SimpNegUnit  : 4
% 2.10/1.27  #BackRed      : 11
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.28  Preprocessing        : 0.29
% 2.10/1.28  Parsing              : 0.15
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.22
% 2.10/1.28  Inferencing          : 0.07
% 2.10/1.28  Reduction            : 0.07
% 2.10/1.28  Demodulation         : 0.05
% 2.10/1.28  BG Simplification    : 0.01
% 2.10/1.28  Subsumption          : 0.04
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.55
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
