%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:53 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 ( 119 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    m1_subset_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_83,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_95,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( r2_hidden(B_23,A_22)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_338,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k3_subset_1(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k3_subset_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_338])).

tff(c_460,plain,(
    ! [D_84,A_85,B_86] :
      ( r2_hidden(D_84,k4_xboole_0(A_85,B_86))
      | r2_hidden(D_84,B_86)
      | ~ r2_hidden(D_84,A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_532,plain,(
    ! [D_89] :
      ( r2_hidden(D_89,k3_subset_1('#skF_5','#skF_6'))
      | r2_hidden(D_89,'#skF_6')
      | ~ r2_hidden(D_89,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_460])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_7',k3_subset_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_554,plain,
    ( r2_hidden('#skF_7','#skF_6')
    | ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_532,c_50])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_554])).

tff(c_573,plain,
    ( ~ m1_subset_1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_569])).

tff(c_576,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_573])).

tff(c_578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_576])).

tff(c_580,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_640,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_2'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,(
    ! [A_110,B_111] :
      ( ~ v1_xboole_0(A_110)
      | r1_tarski(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_640,c_2])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k1_xboole_0
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_711,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k1_xboole_0
      | ~ v1_xboole_0(A_115) ) ),
    inference(resolution,[status(thm)],[c_692,c_32])).

tff(c_721,plain,(
    ! [B_117] : k4_xboole_0('#skF_5',B_117) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_580,c_711])).

tff(c_38,plain,(
    ! [A_21] : k4_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_736,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_38])).

tff(c_749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_736])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  
% 2.63/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.63/1.40  
% 2.63/1.40  %Foreground sorts:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Background operators:
% 2.63/1.40  
% 2.63/1.40  
% 2.63/1.40  %Foreground operators:
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.63/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.40  
% 2.63/1.41  tff(f_90, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 2.63/1.41  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.63/1.41  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.63/1.41  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.63/1.41  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.63/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.63/1.41  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.63/1.41  tff(f_58, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.63/1.41  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.41  tff(c_54, plain, (m1_subset_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.41  tff(c_83, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.41  tff(c_95, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_83])).
% 2.63/1.41  tff(c_96, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_95])).
% 2.63/1.41  tff(c_42, plain, (![B_23, A_22]: (r2_hidden(B_23, A_22) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.63/1.41  tff(c_52, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.41  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.41  tff(c_338, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k3_subset_1(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.63/1.41  tff(c_352, plain, (k4_xboole_0('#skF_5', '#skF_6')=k3_subset_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_338])).
% 2.63/1.41  tff(c_460, plain, (![D_84, A_85, B_86]: (r2_hidden(D_84, k4_xboole_0(A_85, B_86)) | r2_hidden(D_84, B_86) | ~r2_hidden(D_84, A_85))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.63/1.41  tff(c_532, plain, (![D_89]: (r2_hidden(D_89, k3_subset_1('#skF_5', '#skF_6')) | r2_hidden(D_89, '#skF_6') | ~r2_hidden(D_89, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_352, c_460])).
% 2.63/1.41  tff(c_50, plain, (~r2_hidden('#skF_7', k3_subset_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.63/1.41  tff(c_554, plain, (r2_hidden('#skF_7', '#skF_6') | ~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_532, c_50])).
% 2.63/1.41  tff(c_569, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_554])).
% 2.63/1.41  tff(c_573, plain, (~m1_subset_1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_569])).
% 2.63/1.41  tff(c_576, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_573])).
% 2.63/1.41  tff(c_578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_576])).
% 2.63/1.41  tff(c_580, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_95])).
% 2.63/1.41  tff(c_640, plain, (![A_106, B_107]: (r2_hidden('#skF_2'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.63/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.41  tff(c_692, plain, (![A_110, B_111]: (~v1_xboole_0(A_110) | r1_tarski(A_110, B_111))), inference(resolution, [status(thm)], [c_640, c_2])).
% 2.63/1.41  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k1_xboole_0 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.63/1.41  tff(c_711, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k1_xboole_0 | ~v1_xboole_0(A_115))), inference(resolution, [status(thm)], [c_692, c_32])).
% 2.63/1.41  tff(c_721, plain, (![B_117]: (k4_xboole_0('#skF_5', B_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_580, c_711])).
% 2.63/1.41  tff(c_38, plain, (![A_21]: (k4_xboole_0(A_21, k1_xboole_0)=A_21)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.63/1.41  tff(c_736, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_721, c_38])).
% 2.63/1.41  tff(c_749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_736])).
% 2.63/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.41  
% 2.63/1.41  Inference rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Ref     : 0
% 2.63/1.41  #Sup     : 149
% 2.63/1.41  #Fact    : 0
% 2.63/1.41  #Define  : 0
% 2.63/1.41  #Split   : 9
% 2.63/1.41  #Chain   : 0
% 2.63/1.41  #Close   : 0
% 2.63/1.41  
% 2.63/1.41  Ordering : KBO
% 2.63/1.41  
% 2.63/1.41  Simplification rules
% 2.63/1.41  ----------------------
% 2.63/1.41  #Subsume      : 14
% 2.63/1.41  #Demod        : 10
% 2.63/1.41  #Tautology    : 55
% 2.63/1.41  #SimpNegUnit  : 15
% 2.63/1.41  #BackRed      : 0
% 2.63/1.41  
% 2.63/1.41  #Partial instantiations: 0
% 2.63/1.41  #Strategies tried      : 1
% 2.63/1.41  
% 2.63/1.41  Timing (in seconds)
% 2.63/1.41  ----------------------
% 2.63/1.42  Preprocessing        : 0.30
% 2.63/1.42  Parsing              : 0.15
% 2.63/1.42  CNF conversion       : 0.02
% 2.63/1.42  Main loop            : 0.32
% 2.63/1.42  Inferencing          : 0.12
% 2.63/1.42  Reduction            : 0.09
% 2.63/1.42  Demodulation         : 0.06
% 2.63/1.42  BG Simplification    : 0.02
% 2.63/1.42  Subsumption          : 0.06
% 2.63/1.42  Abstraction          : 0.01
% 2.63/1.42  MUC search           : 0.00
% 2.63/1.42  Cooper               : 0.00
% 2.63/1.42  Total                : 0.65
% 2.63/1.42  Index Insertion      : 0.00
% 2.63/1.42  Index Deletion       : 0.00
% 2.63/1.42  Index Matching       : 0.00
% 2.63/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
