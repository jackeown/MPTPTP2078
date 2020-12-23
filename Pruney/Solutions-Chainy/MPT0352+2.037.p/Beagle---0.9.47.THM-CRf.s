%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:51 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 112 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 196 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_42,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_36,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_186,plain,(
    ! [A_45,B_46] :
      ( k3_subset_1(A_45,k3_subset_1(A_45,B_46)) = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_198,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_186])).

tff(c_99,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_99])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [B_34,A_35] :
      ( m1_subset_1(B_34,A_35)
      | ~ r2_hidden(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,(
    ! [C_10,A_6] :
      ( m1_subset_1(C_10,k1_zfmisc_1(A_6))
      | v1_xboole_0(k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_88])).

tff(c_129,plain,(
    ! [C_38,A_39] :
      ( m1_subset_1(C_38,k1_zfmisc_1(A_39))
      | ~ r1_tarski(C_38,A_39) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_94])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_142,plain,(
    ! [A_40,C_41] :
      ( k4_xboole_0(A_40,C_41) = k3_subset_1(A_40,C_41)
      | ~ r1_tarski(C_41,A_40) ) ),
    inference(resolution,[status(thm)],[c_129,c_26])).

tff(c_346,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_subset_1(A_57,k4_xboole_0(A_57,B_58)) ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_392,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_346])).

tff(c_399,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_111,c_392])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_199,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_32,c_186])).

tff(c_112,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_123,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_4])).

tff(c_161,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_123,c_142])).

tff(c_317,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_161])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( r1_tarski(k4_xboole_0(C_3,B_2),k4_xboole_0(C_3,A_1))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_542,plain,(
    ! [B_69] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_69),'#skF_5')
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_2])).

tff(c_548,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_542])).

tff(c_564,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_548])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_564])).

tff(c_567,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_570,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_36])).

tff(c_606,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k3_subset_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_623,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_606])).

tff(c_622,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_606])).

tff(c_773,plain,(
    ! [B_87] :
      ( r1_tarski(k4_xboole_0('#skF_3',B_87),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski('#skF_4',B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_2])).

tff(c_779,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_773])).

tff(c_785,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_779])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.36  
% 2.83/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.83/1.36  
% 2.83/1.36  %Foreground sorts:
% 2.83/1.36  
% 2.83/1.36  
% 2.83/1.36  %Background operators:
% 2.83/1.36  
% 2.83/1.36  
% 2.83/1.36  %Foreground operators:
% 2.83/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.83/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.83/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.83/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.36  
% 2.83/1.38  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.83/1.38  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.83/1.38  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.83/1.38  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.83/1.38  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.83/1.38  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.83/1.38  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.83/1.38  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.83/1.38  tff(c_42, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.38  tff(c_73, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 2.83/1.38  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.38  tff(c_128, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_36])).
% 2.83/1.38  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.38  tff(c_186, plain, (![A_45, B_46]: (k3_subset_1(A_45, k3_subset_1(A_45, B_46))=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.83/1.38  tff(c_198, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_34, c_186])).
% 2.83/1.38  tff(c_99, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.38  tff(c_111, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_99])).
% 2.83/1.38  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.38  tff(c_28, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.38  tff(c_8, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.83/1.38  tff(c_88, plain, (![B_34, A_35]: (m1_subset_1(B_34, A_35) | ~r2_hidden(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.83/1.38  tff(c_94, plain, (![C_10, A_6]: (m1_subset_1(C_10, k1_zfmisc_1(A_6)) | v1_xboole_0(k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(resolution, [status(thm)], [c_8, c_88])).
% 2.83/1.38  tff(c_129, plain, (![C_38, A_39]: (m1_subset_1(C_38, k1_zfmisc_1(A_39)) | ~r1_tarski(C_38, A_39))), inference(negUnitSimplification, [status(thm)], [c_28, c_94])).
% 2.83/1.38  tff(c_26, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.38  tff(c_142, plain, (![A_40, C_41]: (k4_xboole_0(A_40, C_41)=k3_subset_1(A_40, C_41) | ~r1_tarski(C_41, A_40))), inference(resolution, [status(thm)], [c_129, c_26])).
% 2.83/1.38  tff(c_346, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_subset_1(A_57, k4_xboole_0(A_57, B_58)))), inference(resolution, [status(thm)], [c_4, c_142])).
% 2.83/1.38  tff(c_392, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k4_xboole_0('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_111, c_346])).
% 2.83/1.38  tff(c_399, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_198, c_111, c_392])).
% 2.83/1.38  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.83/1.38  tff(c_199, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_32, c_186])).
% 2.83/1.38  tff(c_112, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_99])).
% 2.83/1.38  tff(c_123, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_112, c_4])).
% 2.83/1.38  tff(c_161, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_123, c_142])).
% 2.83/1.38  tff(c_317, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_199, c_161])).
% 2.83/1.38  tff(c_2, plain, (![C_3, B_2, A_1]: (r1_tarski(k4_xboole_0(C_3, B_2), k4_xboole_0(C_3, A_1)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.83/1.38  tff(c_542, plain, (![B_69]: (r1_tarski(k4_xboole_0('#skF_3', B_69), '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), B_69))), inference(superposition, [status(thm), theory('equality')], [c_317, c_2])).
% 2.83/1.38  tff(c_548, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_399, c_542])).
% 2.83/1.38  tff(c_564, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_548])).
% 2.83/1.38  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_564])).
% 2.83/1.38  tff(c_567, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_42])).
% 2.83/1.38  tff(c_570, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_36])).
% 2.83/1.38  tff(c_606, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k3_subset_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.83/1.38  tff(c_623, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_606])).
% 2.83/1.38  tff(c_622, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_606])).
% 2.83/1.38  tff(c_773, plain, (![B_87]: (r1_tarski(k4_xboole_0('#skF_3', B_87), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', B_87))), inference(superposition, [status(thm), theory('equality')], [c_622, c_2])).
% 2.83/1.38  tff(c_779, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_623, c_773])).
% 2.83/1.38  tff(c_785, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_779])).
% 2.83/1.38  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_785])).
% 2.83/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.38  
% 2.83/1.38  Inference rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Ref     : 0
% 2.83/1.38  #Sup     : 184
% 2.83/1.38  #Fact    : 0
% 2.83/1.38  #Define  : 0
% 2.83/1.38  #Split   : 6
% 2.83/1.38  #Chain   : 0
% 2.83/1.38  #Close   : 0
% 2.83/1.38  
% 2.83/1.38  Ordering : KBO
% 2.83/1.38  
% 2.83/1.38  Simplification rules
% 2.83/1.38  ----------------------
% 2.83/1.38  #Subsume      : 16
% 2.83/1.38  #Demod        : 55
% 2.83/1.38  #Tautology    : 75
% 2.83/1.38  #SimpNegUnit  : 5
% 2.83/1.38  #BackRed      : 0
% 2.83/1.38  
% 2.83/1.38  #Partial instantiations: 0
% 2.83/1.38  #Strategies tried      : 1
% 2.83/1.38  
% 2.83/1.38  Timing (in seconds)
% 2.83/1.38  ----------------------
% 2.83/1.38  Preprocessing        : 0.29
% 2.83/1.38  Parsing              : 0.14
% 2.83/1.38  CNF conversion       : 0.02
% 2.83/1.38  Main loop            : 0.33
% 2.83/1.38  Inferencing          : 0.12
% 2.83/1.38  Reduction            : 0.10
% 2.83/1.38  Demodulation         : 0.06
% 2.83/1.38  BG Simplification    : 0.02
% 2.83/1.38  Subsumption          : 0.06
% 2.83/1.38  Abstraction          : 0.02
% 2.83/1.38  MUC search           : 0.00
% 2.83/1.38  Cooper               : 0.00
% 2.83/1.38  Total                : 0.65
% 2.83/1.38  Index Insertion      : 0.00
% 2.83/1.38  Index Deletion       : 0.00
% 2.83/1.38  Index Matching       : 0.00
% 2.83/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
