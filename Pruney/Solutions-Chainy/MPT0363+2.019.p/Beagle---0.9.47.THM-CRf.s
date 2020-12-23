%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 ( 122 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4'))
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_31,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_47,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_30])).

tff(c_20,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_120,plain,(
    ! [A_55,B_56] :
      ( k4_xboole_0(A_55,B_56) = k3_subset_1(A_55,B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_120])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_xboole_0(A_6,C_8)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_244,plain,(
    ! [A_68] :
      ( r1_xboole_0(A_68,'#skF_4')
      | ~ r1_tarski(A_68,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_259,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_47,c_244])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_259])).

tff(c_273,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_355,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_366,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_355])).

tff(c_434,plain,(
    ! [A_109,B_110,C_111] :
      ( r1_tarski(A_109,k4_xboole_0(B_110,C_111))
      | ~ r1_xboole_0(A_109,C_111)
      | ~ r1_tarski(A_109,B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_569,plain,(
    ! [A_130] :
      ( r1_tarski(A_130,k3_subset_1('#skF_2','#skF_4'))
      | ~ r1_xboole_0(A_130,'#skF_4')
      | ~ r1_tarski(A_130,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_434])).

tff(c_272,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_578,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_569,c_272])).

tff(c_583,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_578])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_337,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(A_103,k3_subset_1(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_346,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_337])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_591,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(A_136,k3_subset_1(A_136,B_137)) = k3_subset_1(A_136,k3_subset_1(A_136,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(resolution,[status(thm)],[c_16,c_355])).

tff(c_597,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_591])).

tff(c_602,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_597])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_279,plain,(
    ! [A_77,B_78] :
      ( ~ r2_hidden('#skF_1'(A_77,B_78),B_78)
      | r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_285,plain,(
    ! [A_79] : r1_tarski(A_79,A_79) ),
    inference(resolution,[status(thm)],[c_6,c_279])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_tarski(A_6,B_7)
      | ~ r1_tarski(A_6,k4_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_294,plain,(
    ! [B_7,C_8] : r1_tarski(k4_xboole_0(B_7,C_8),B_7) ),
    inference(resolution,[status(thm)],[c_285,c_10])).

tff(c_661,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_294])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.37  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.53/1.37  
% 2.53/1.37  %Foreground sorts:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Background operators:
% 2.53/1.37  
% 2.53/1.37  
% 2.53/1.37  %Foreground operators:
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.53/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.53/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.53/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.53/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.37  
% 2.81/1.38  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.81/1.38  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.81/1.38  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.81/1.38  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.81/1.38  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.81/1.38  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.81/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.38  tff(c_24, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.38  tff(c_31, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.81/1.38  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.38  tff(c_47, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_31, c_30])).
% 2.81/1.38  tff(c_20, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.38  tff(c_120, plain, (![A_55, B_56]: (k4_xboole_0(A_55, B_56)=k3_subset_1(A_55, B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.38  tff(c_131, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_120])).
% 2.81/1.38  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_xboole_0(A_6, C_8) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.38  tff(c_244, plain, (![A_68]: (r1_xboole_0(A_68, '#skF_4') | ~r1_tarski(A_68, k3_subset_1('#skF_2', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 2.81/1.38  tff(c_259, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_47, c_244])).
% 2.81/1.38  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_259])).
% 2.81/1.38  tff(c_273, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_24])).
% 2.81/1.38  tff(c_355, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.38  tff(c_366, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_355])).
% 2.81/1.38  tff(c_434, plain, (![A_109, B_110, C_111]: (r1_tarski(A_109, k4_xboole_0(B_110, C_111)) | ~r1_xboole_0(A_109, C_111) | ~r1_tarski(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.81/1.38  tff(c_569, plain, (![A_130]: (r1_tarski(A_130, k3_subset_1('#skF_2', '#skF_4')) | ~r1_xboole_0(A_130, '#skF_4') | ~r1_tarski(A_130, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_366, c_434])).
% 2.81/1.38  tff(c_272, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_24])).
% 2.81/1.38  tff(c_578, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_569, c_272])).
% 2.81/1.38  tff(c_583, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_578])).
% 2.81/1.38  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.38  tff(c_337, plain, (![A_103, B_104]: (k3_subset_1(A_103, k3_subset_1(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.38  tff(c_346, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22, c_337])).
% 2.81/1.38  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.81/1.38  tff(c_591, plain, (![A_136, B_137]: (k4_xboole_0(A_136, k3_subset_1(A_136, B_137))=k3_subset_1(A_136, k3_subset_1(A_136, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(resolution, [status(thm)], [c_16, c_355])).
% 2.81/1.38  tff(c_597, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_591])).
% 2.81/1.38  tff(c_602, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_597])).
% 2.81/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.38  tff(c_279, plain, (![A_77, B_78]: (~r2_hidden('#skF_1'(A_77, B_78), B_78) | r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.38  tff(c_285, plain, (![A_79]: (r1_tarski(A_79, A_79))), inference(resolution, [status(thm)], [c_6, c_279])).
% 2.81/1.38  tff(c_10, plain, (![A_6, B_7, C_8]: (r1_tarski(A_6, B_7) | ~r1_tarski(A_6, k4_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.38  tff(c_294, plain, (![B_7, C_8]: (r1_tarski(k4_xboole_0(B_7, C_8), B_7))), inference(resolution, [status(thm)], [c_285, c_10])).
% 2.81/1.38  tff(c_661, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_602, c_294])).
% 2.81/1.38  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_661])).
% 2.81/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.38  
% 2.81/1.38  Inference rules
% 2.81/1.38  ----------------------
% 2.81/1.38  #Ref     : 0
% 2.81/1.38  #Sup     : 156
% 2.81/1.38  #Fact    : 0
% 2.81/1.38  #Define  : 0
% 2.81/1.39  #Split   : 1
% 2.81/1.39  #Chain   : 0
% 2.81/1.39  #Close   : 0
% 2.81/1.39  
% 2.81/1.39  Ordering : KBO
% 2.81/1.39  
% 2.81/1.39  Simplification rules
% 2.81/1.39  ----------------------
% 2.81/1.39  #Subsume      : 0
% 2.81/1.39  #Demod        : 23
% 2.81/1.39  #Tautology    : 51
% 2.81/1.39  #SimpNegUnit  : 4
% 2.81/1.39  #BackRed      : 0
% 2.81/1.39  
% 2.81/1.39  #Partial instantiations: 0
% 2.81/1.39  #Strategies tried      : 1
% 2.81/1.39  
% 2.81/1.39  Timing (in seconds)
% 2.81/1.39  ----------------------
% 2.81/1.39  Preprocessing        : 0.29
% 2.81/1.39  Parsing              : 0.16
% 2.81/1.39  CNF conversion       : 0.02
% 2.81/1.39  Main loop            : 0.34
% 2.81/1.39  Inferencing          : 0.13
% 2.81/1.39  Reduction            : 0.10
% 2.81/1.39  Demodulation         : 0.07
% 2.81/1.39  BG Simplification    : 0.02
% 2.81/1.39  Subsumption          : 0.06
% 2.81/1.39  Abstraction          : 0.02
% 2.81/1.39  MUC search           : 0.00
% 2.81/1.39  Cooper               : 0.00
% 2.81/1.39  Total                : 0.66
% 2.81/1.39  Index Insertion      : 0.00
% 2.81/1.39  Index Deletion       : 0.00
% 2.81/1.39  Index Matching       : 0.00
% 2.81/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
