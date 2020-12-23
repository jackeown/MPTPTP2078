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
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 119 expanded)
%              Number of leaves         :   32 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 161 expanded)
%              Number of equality atoms :   32 (  78 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_72,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_80])).

tff(c_154,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_86,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_211,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_87])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_240,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | k4_xboole_0(A_54,B_55) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_42])).

tff(c_244,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_240,c_154])).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_647,plain,(
    ! [A_102,B_103] :
      ( k4_xboole_0(A_102,B_103) = k3_subset_1(A_102,B_103)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_660,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_647])).

tff(c_50,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [A_47,B_48] : k4_xboole_0(k4_xboole_0(A_47,B_48),A_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_133])).

tff(c_137,plain,(
    ! [A_23,B_24] : k4_xboole_0(k4_xboole_0(A_23,B_24),A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_133])).

tff(c_141,plain,(
    ! [A_47,B_48] : k4_xboole_0(k1_xboole_0,k4_xboole_0(A_47,B_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_137])).

tff(c_274,plain,(
    ! [A_47,B_48] : k4_xboole_0('#skF_9',k4_xboole_0(A_47,B_48)) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_211,c_141])).

tff(c_674,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_274])).

tff(c_686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_674])).

tff(c_687,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_688,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_792,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_811,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_688,c_792])).

tff(c_1104,plain,(
    ! [D_139,B_140,A_141] :
      ( r2_hidden(D_139,B_140)
      | ~ r2_hidden(D_139,k3_xboole_0(A_141,B_140)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2251,plain,(
    ! [D_189] :
      ( r2_hidden(D_189,k3_subset_1('#skF_8','#skF_9'))
      | ~ r2_hidden(D_189,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_811,c_1104])).

tff(c_1248,plain,(
    ! [A_147,B_148] :
      ( k4_xboole_0(A_147,B_148) = k3_subset_1(A_147,B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1257,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_1248])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1265,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_9')
      | ~ r2_hidden(D_14,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_24])).

tff(c_2272,plain,(
    ! [D_190] : ~ r2_hidden(D_190,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2251,c_1265])).

tff(c_2284,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_2272])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_687,c_2284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.67/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.66  
% 3.67/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 3.67/1.66  
% 3.67/1.66  %Foreground sorts:
% 3.67/1.66  
% 3.67/1.66  
% 3.67/1.66  %Background operators:
% 3.67/1.66  
% 3.67/1.66  
% 3.67/1.66  %Foreground operators:
% 3.67/1.66  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.67/1.66  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.67/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.67/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.67/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.67/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.67/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.67/1.66  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.67/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.67/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.67/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.67/1.66  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.67/1.66  tff('#skF_9', type, '#skF_9': $i).
% 3.67/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.67/1.66  tff('#skF_8', type, '#skF_8': $i).
% 3.67/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.67/1.66  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.67/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.67/1.66  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.67/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.67/1.66  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.67/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.67/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.67/1.66  
% 3.67/1.67  tff(f_88, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.67/1.67  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.67/1.67  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.67/1.67  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.67/1.67  tff(f_66, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.67/1.67  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.67/1.67  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.67/1.67  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.67/1.67  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.67/1.67  tff(c_72, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.67/1.67  tff(c_80, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.67/1.67  tff(c_88, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_80])).
% 3.67/1.67  tff(c_154, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_88])).
% 3.67/1.67  tff(c_86, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.67/1.67  tff(c_87, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_86])).
% 3.67/1.67  tff(c_211, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_154, c_87])).
% 3.67/1.67  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.67/1.67  tff(c_240, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | k4_xboole_0(A_54, B_55)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_42])).
% 3.67/1.67  tff(c_244, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))!='#skF_9'), inference(resolution, [status(thm)], [c_240, c_154])).
% 3.67/1.67  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.67/1.67  tff(c_647, plain, (![A_102, B_103]: (k4_xboole_0(A_102, B_103)=k3_subset_1(A_102, B_103) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.67  tff(c_660, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_647])).
% 3.67/1.67  tff(c_50, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.67/1.67  tff(c_133, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.67/1.67  tff(c_138, plain, (![A_47, B_48]: (k4_xboole_0(k4_xboole_0(A_47, B_48), A_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_133])).
% 3.67/1.67  tff(c_137, plain, (![A_23, B_24]: (k4_xboole_0(k4_xboole_0(A_23, B_24), A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_133])).
% 3.67/1.67  tff(c_141, plain, (![A_47, B_48]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(A_47, B_48))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_138, c_137])).
% 3.67/1.67  tff(c_274, plain, (![A_47, B_48]: (k4_xboole_0('#skF_9', k4_xboole_0(A_47, B_48))='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_211, c_141])).
% 3.67/1.67  tff(c_674, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_660, c_274])).
% 3.67/1.67  tff(c_686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_674])).
% 3.67/1.67  tff(c_687, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 3.67/1.67  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.67/1.67  tff(c_688, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_88])).
% 3.67/1.67  tff(c_792, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=A_108 | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.67/1.67  tff(c_811, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_688, c_792])).
% 3.67/1.67  tff(c_1104, plain, (![D_139, B_140, A_141]: (r2_hidden(D_139, B_140) | ~r2_hidden(D_139, k3_xboole_0(A_141, B_140)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.67/1.67  tff(c_2251, plain, (![D_189]: (r2_hidden(D_189, k3_subset_1('#skF_8', '#skF_9')) | ~r2_hidden(D_189, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_811, c_1104])).
% 3.67/1.67  tff(c_1248, plain, (![A_147, B_148]: (k4_xboole_0(A_147, B_148)=k3_subset_1(A_147, B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(A_147)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.67/1.67  tff(c_1257, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_1248])).
% 3.67/1.67  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.67/1.67  tff(c_1265, plain, (![D_14]: (~r2_hidden(D_14, '#skF_9') | ~r2_hidden(D_14, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_24])).
% 3.67/1.67  tff(c_2272, plain, (![D_190]: (~r2_hidden(D_190, '#skF_9'))), inference(resolution, [status(thm)], [c_2251, c_1265])).
% 3.67/1.67  tff(c_2284, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_2272])).
% 3.67/1.67  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_687, c_2284])).
% 3.67/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.67/1.67  
% 3.67/1.67  Inference rules
% 3.67/1.67  ----------------------
% 3.67/1.67  #Ref     : 0
% 3.67/1.67  #Sup     : 580
% 3.67/1.67  #Fact    : 0
% 3.67/1.67  #Define  : 0
% 3.67/1.67  #Split   : 5
% 3.67/1.67  #Chain   : 0
% 3.67/1.67  #Close   : 0
% 3.67/1.67  
% 3.67/1.67  Ordering : KBO
% 3.67/1.67  
% 3.67/1.67  Simplification rules
% 3.67/1.67  ----------------------
% 3.67/1.67  #Subsume      : 76
% 3.67/1.67  #Demod        : 225
% 3.67/1.67  #Tautology    : 332
% 3.67/1.67  #SimpNegUnit  : 16
% 3.67/1.67  #BackRed      : 10
% 3.67/1.67  
% 3.67/1.67  #Partial instantiations: 0
% 3.67/1.67  #Strategies tried      : 1
% 3.67/1.67  
% 3.67/1.67  Timing (in seconds)
% 3.67/1.67  ----------------------
% 3.67/1.67  Preprocessing        : 0.35
% 3.67/1.68  Parsing              : 0.18
% 3.67/1.68  CNF conversion       : 0.03
% 3.67/1.68  Main loop            : 0.56
% 3.67/1.68  Inferencing          : 0.19
% 3.67/1.68  Reduction            : 0.19
% 3.67/1.68  Demodulation         : 0.14
% 3.67/1.68  BG Simplification    : 0.03
% 3.67/1.68  Subsumption          : 0.10
% 3.67/1.68  Abstraction          : 0.03
% 3.67/1.68  MUC search           : 0.00
% 3.67/1.68  Cooper               : 0.00
% 3.67/1.68  Total                : 0.94
% 3.67/1.68  Index Insertion      : 0.00
% 3.67/1.68  Index Deletion       : 0.00
% 3.67/1.68  Index Matching       : 0.00
% 3.67/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
