%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:41 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   60 (  94 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 163 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    ~ r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_30])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,(
    ! [A_53,B_54] :
      ( k3_subset_1(A_53,k3_subset_1(A_53,B_54)) = B_54
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_94])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_120,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_432,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,k3_subset_1(A_105,B_106)) = k3_subset_1(A_105,k3_subset_1(A_105,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(resolution,[status(thm)],[c_16,c_120])).

tff(c_436,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_432])).

tff(c_441,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_436])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_901,plain,(
    ! [A_130] :
      ( r1_xboole_0(A_130,k3_subset_1('#skF_2','#skF_4'))
      | ~ r1_tarski(A_130,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_8])).

tff(c_904,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_901,c_31])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_904])).

tff(c_909,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_974,plain,(
    ! [A_165,B_166] :
      ( k3_subset_1(A_165,k3_subset_1(A_165,B_166)) = B_166
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_983,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_974])).

tff(c_984,plain,(
    ! [A_167,B_168] :
      ( k4_xboole_0(A_167,B_168) = k3_subset_1(A_167,B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1353,plain,(
    ! [A_227,B_228] :
      ( k4_xboole_0(A_227,k3_subset_1(A_227,B_228)) = k3_subset_1(A_227,k3_subset_1(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_16,c_984])).

tff(c_1359,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1353])).

tff(c_1364,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_1359])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_916,plain,(
    ! [A_139,B_140] :
      ( ~ r2_hidden('#skF_1'(A_139,B_140),B_140)
      | r1_tarski(A_139,B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_926,plain,(
    ! [A_144] : r1_tarski(A_144,A_144) ),
    inference(resolution,[status(thm)],[c_6,c_916])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_936,plain,(
    ! [B_7,C_8] : r1_tarski(k4_xboole_0(B_7,C_8),B_7) ),
    inference(resolution,[status(thm)],[c_926,c_10])).

tff(c_1432,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1364,c_936])).

tff(c_911,plain,(
    r1_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_909,c_30])).

tff(c_982,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_20,c_974])).

tff(c_1357,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_1353])).

tff(c_1362,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_1357])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_tarski(A_9,k4_xboole_0(B_10,C_11))
      | ~ r1_xboole_0(A_9,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1882,plain,(
    ! [A_261] :
      ( r1_tarski(A_261,'#skF_4')
      | ~ r1_xboole_0(A_261,k3_subset_1('#skF_2','#skF_4'))
      | ~ r1_tarski(A_261,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1362,c_12])).

tff(c_1913,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_911,c_1882])).

tff(c_1930,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1432,c_1913])).

tff(c_1932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_909,c_1930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:33:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.88  
% 4.54/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.54/1.88  
% 4.54/1.88  %Foreground sorts:
% 4.54/1.88  
% 4.54/1.88  
% 4.54/1.88  %Background operators:
% 4.54/1.88  
% 4.54/1.88  
% 4.54/1.88  %Foreground operators:
% 4.54/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.88  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.54/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.54/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.88  
% 4.54/1.90  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 4.54/1.90  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.54/1.90  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.54/1.90  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.54/1.90  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.54/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.54/1.90  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.54/1.90  tff(c_24, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.90  tff(c_31, plain, (~r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_24])).
% 4.54/1.90  tff(c_30, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.90  tff(c_47, plain, (r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_31, c_30])).
% 4.54/1.90  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.90  tff(c_94, plain, (![A_53, B_54]: (k3_subset_1(A_53, k3_subset_1(A_53, B_54))=B_54 | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.54/1.90  tff(c_102, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_20, c_94])).
% 4.54/1.90  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.54/1.90  tff(c_120, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.54/1.90  tff(c_432, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k3_subset_1(A_105, B_106))=k3_subset_1(A_105, k3_subset_1(A_105, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(resolution, [status(thm)], [c_16, c_120])).
% 4.54/1.90  tff(c_436, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_432])).
% 4.54/1.90  tff(c_441, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_436])).
% 4.54/1.90  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.54/1.90  tff(c_901, plain, (![A_130]: (r1_xboole_0(A_130, k3_subset_1('#skF_2', '#skF_4')) | ~r1_tarski(A_130, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_441, c_8])).
% 4.54/1.90  tff(c_904, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_901, c_31])).
% 4.54/1.90  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_904])).
% 4.54/1.90  tff(c_909, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 4.54/1.90  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.90  tff(c_974, plain, (![A_165, B_166]: (k3_subset_1(A_165, k3_subset_1(A_165, B_166))=B_166 | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.54/1.90  tff(c_983, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22, c_974])).
% 4.54/1.90  tff(c_984, plain, (![A_167, B_168]: (k4_xboole_0(A_167, B_168)=k3_subset_1(A_167, B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(A_167)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.54/1.90  tff(c_1353, plain, (![A_227, B_228]: (k4_xboole_0(A_227, k3_subset_1(A_227, B_228))=k3_subset_1(A_227, k3_subset_1(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(resolution, [status(thm)], [c_16, c_984])).
% 4.54/1.90  tff(c_1359, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1353])).
% 4.54/1.90  tff(c_1364, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_983, c_1359])).
% 4.54/1.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.90  tff(c_916, plain, (![A_139, B_140]: (~r2_hidden('#skF_1'(A_139, B_140), B_140) | r1_tarski(A_139, B_140))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.90  tff(c_926, plain, (![A_144]: (r1_tarski(A_144, A_144))), inference(resolution, [status(thm)], [c_6, c_916])).
% 4.54/1.90  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, B_7) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.54/1.90  tff(c_936, plain, (![B_7, C_8]: (r1_tarski(k4_xboole_0(B_7, C_8), B_7))), inference(resolution, [status(thm)], [c_926, c_10])).
% 4.54/1.90  tff(c_1432, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1364, c_936])).
% 4.54/1.90  tff(c_911, plain, (r1_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_909, c_30])).
% 4.54/1.90  tff(c_982, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_20, c_974])).
% 4.54/1.90  tff(c_1357, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_1353])).
% 4.54/1.90  tff(c_1362, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_982, c_1357])).
% 4.54/1.90  tff(c_12, plain, (![A_9, B_10, C_11]: (r1_tarski(A_9, k4_xboole_0(B_10, C_11)) | ~r1_xboole_0(A_9, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.54/1.90  tff(c_1882, plain, (![A_261]: (r1_tarski(A_261, '#skF_4') | ~r1_xboole_0(A_261, k3_subset_1('#skF_2', '#skF_4')) | ~r1_tarski(A_261, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1362, c_12])).
% 4.54/1.90  tff(c_1913, plain, (r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_911, c_1882])).
% 4.54/1.90  tff(c_1930, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1432, c_1913])).
% 4.54/1.90  tff(c_1932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_909, c_1930])).
% 4.54/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.90  
% 4.54/1.90  Inference rules
% 4.54/1.90  ----------------------
% 4.54/1.90  #Ref     : 0
% 4.54/1.90  #Sup     : 471
% 4.54/1.90  #Fact    : 0
% 4.54/1.90  #Define  : 0
% 4.54/1.90  #Split   : 1
% 4.54/1.90  #Chain   : 0
% 4.54/1.90  #Close   : 0
% 4.54/1.90  
% 4.54/1.90  Ordering : KBO
% 4.54/1.90  
% 4.54/1.90  Simplification rules
% 4.54/1.90  ----------------------
% 4.54/1.90  #Subsume      : 4
% 4.54/1.90  #Demod        : 84
% 4.54/1.90  #Tautology    : 112
% 4.54/1.90  #SimpNegUnit  : 3
% 4.54/1.90  #BackRed      : 0
% 4.54/1.90  
% 4.54/1.90  #Partial instantiations: 0
% 4.54/1.90  #Strategies tried      : 1
% 4.54/1.90  
% 4.54/1.90  Timing (in seconds)
% 4.54/1.90  ----------------------
% 4.54/1.90  Preprocessing        : 0.31
% 4.54/1.90  Parsing              : 0.17
% 4.54/1.90  CNF conversion       : 0.02
% 4.54/1.90  Main loop            : 0.77
% 4.54/1.90  Inferencing          : 0.29
% 4.54/1.90  Reduction            : 0.25
% 4.54/1.90  Demodulation         : 0.18
% 4.54/1.90  BG Simplification    : 0.03
% 4.54/1.90  Subsumption          : 0.15
% 4.54/1.90  Abstraction          : 0.03
% 4.54/1.90  MUC search           : 0.00
% 4.54/1.90  Cooper               : 0.00
% 4.54/1.91  Total                : 1.12
% 4.54/1.91  Index Insertion      : 0.00
% 4.54/1.91  Index Deletion       : 0.00
% 4.54/1.91  Index Matching       : 0.00
% 4.54/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
