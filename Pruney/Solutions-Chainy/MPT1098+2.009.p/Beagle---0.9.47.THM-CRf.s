%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:27 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.29s
% Verified   : 
% Statistics : Number of formulae       :   53 (  86 expanded)
%              Number of leaves         :   20 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 189 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_finset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( v1_finset_1(A)
          & r1_tarski(A,k2_zfmisc_1(B,C))
          & ! [D] :
              ~ ( v1_finset_1(D)
                & r1_tarski(D,B)
                & r1_tarski(A,k2_zfmisc_1(D,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_finset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( v1_finset_1(A)
        & r1_tarski(A,k2_zfmisc_1(B,C))
        & ! [D,E] :
            ~ ( v1_finset_1(D)
              & r1_tarski(D,B)
              & v1_finset_1(E)
              & r1_tarski(E,C)
              & r1_tarski(A,k2_zfmisc_1(D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_finset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( r1_tarski(A,k2_zfmisc_1(C,D))
        & r1_tarski(B,k2_zfmisc_1(E,F)) )
     => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(c_28,plain,(
    v1_finset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_369,plain,(
    ! [A_65,B_66,C_67] :
      ( v1_finset_1('#skF_2'(A_65,B_66,C_67))
      | ~ r1_tarski(A_65,k2_zfmisc_1(B_66,C_67))
      | ~ v1_finset_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_376,plain,
    ( v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_369])).

tff(c_380,plain,(
    v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_376])).

tff(c_863,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski('#skF_2'(A_100,B_101,C_102),B_101)
      | ~ r1_tarski(A_100,k2_zfmisc_1(B_101,C_102))
      | ~ v1_finset_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1503,plain,(
    ! [A_135,B_136,C_137] :
      ( k2_xboole_0('#skF_2'(A_135,B_136,C_137),B_136) = B_136
      | ~ r1_tarski(A_135,k2_zfmisc_1(B_136,C_137))
      | ~ v1_finset_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_863,c_10])).

tff(c_1523,plain,
    ( k2_xboole_0('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') = '#skF_5'
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1503])).

tff(c_1535,plain,(
    k2_xboole_0('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1523])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_31,B_32] :
      ( ~ r2_hidden('#skF_1'(A_31,B_32),B_32)
      | r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_33] : r1_tarski(A_33,A_33) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(k2_xboole_0(A_6,B_7),C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_50,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_42,c_8])).

tff(c_1578,plain,(
    r1_tarski('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1535,c_50])).

tff(c_14,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_zfmisc_1('#skF_2'(A_17,B_18,C_19),'#skF_3'(A_17,B_18,C_19)))
      | ~ r1_tarski(A_17,k2_zfmisc_1(B_18,C_19))
      | ~ v1_finset_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_720,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski('#skF_3'(A_88,B_89,C_90),C_90)
      | ~ r1_tarski(A_88,k2_zfmisc_1(B_89,C_90))
      | ~ v1_finset_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1199,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_xboole_0('#skF_3'(A_123,B_124,C_125),C_125) = C_125
      | ~ r1_tarski(A_123,k2_zfmisc_1(B_124,C_125))
      | ~ v1_finset_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_720,c_10])).

tff(c_1214,plain,
    ( k2_xboole_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_6') = '#skF_6'
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1199])).

tff(c_1222,plain,(
    k2_xboole_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1214])).

tff(c_51,plain,(
    ! [A_33] : k2_xboole_0(A_33,A_33) = A_33 ),
    inference(resolution,[status(thm)],[c_42,c_10])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_1116,plain,(
    ! [A_119,F_117,E_122,D_121,B_120,C_118] :
      ( r1_tarski(k2_xboole_0(A_119,B_120),k2_zfmisc_1(k2_xboole_0(C_118,E_122),k2_xboole_0(D_121,F_117)))
      | ~ r1_tarski(B_120,k2_zfmisc_1(E_122,F_117))
      | ~ r1_tarski(A_119,k2_zfmisc_1(C_118,D_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2561,plain,(
    ! [E_174,D_176,A_175,C_172,B_173,F_171] :
      ( r1_tarski(A_175,k2_zfmisc_1(k2_xboole_0(C_172,E_174),k2_xboole_0(D_176,F_171)))
      | ~ r1_tarski(B_173,k2_zfmisc_1(E_174,F_171))
      | ~ r1_tarski(A_175,k2_zfmisc_1(C_172,D_176)) ) ),
    inference(resolution,[status(thm)],[c_1116,c_8])).

tff(c_4863,plain,(
    ! [E_266,A_267,F_268,C_270,D_269] :
      ( r1_tarski(A_267,k2_zfmisc_1(k2_xboole_0(C_270,E_266),k2_xboole_0(D_269,F_268)))
      | ~ r1_tarski(A_267,k2_zfmisc_1(C_270,D_269)) ) ),
    inference(resolution,[status(thm)],[c_41,c_2561])).

tff(c_5032,plain,(
    ! [A_271,A_272,D_273,F_274] :
      ( r1_tarski(A_271,k2_zfmisc_1(A_272,k2_xboole_0(D_273,F_274)))
      | ~ r1_tarski(A_271,k2_zfmisc_1(A_272,D_273)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_4863])).

tff(c_5527,plain,(
    ! [A_289,A_290] :
      ( r1_tarski(A_289,k2_zfmisc_1(A_290,'#skF_6'))
      | ~ r1_tarski(A_289,k2_zfmisc_1(A_290,'#skF_3'('#skF_4','#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1222,c_5032])).

tff(c_5563,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_6'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1('#skF_5','#skF_6'))
    | ~ v1_finset_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_5527])).

tff(c_5586,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_5563])).

tff(c_24,plain,(
    ! [D_23] :
      ( ~ r1_tarski('#skF_4',k2_zfmisc_1(D_23,'#skF_6'))
      | ~ r1_tarski(D_23,'#skF_5')
      | ~ v1_finset_1(D_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5612,plain,
    ( ~ r1_tarski('#skF_2'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | ~ v1_finset_1('#skF_2'('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_5586,c_24])).

tff(c_5637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_1578,c_5612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:14:59 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.01/2.28  
% 6.01/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.01/2.29  %$ r2_hidden > r1_tarski > v1_finset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.01/2.29  
% 6.01/2.29  %Foreground sorts:
% 6.01/2.29  
% 6.01/2.29  
% 6.01/2.29  %Background operators:
% 6.01/2.29  
% 6.01/2.29  
% 6.01/2.29  %Foreground operators:
% 6.01/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.01/2.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.01/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.01/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.01/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.01/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.01/2.29  tff('#skF_4', type, '#skF_4': $i).
% 6.01/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.01/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.01/2.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.01/2.29  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 6.01/2.29  
% 6.29/2.31  tff(f_77, negated_conjecture, ~(![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D]: ~((v1_finset_1(D) & r1_tarski(D, B)) & r1_tarski(A, k2_zfmisc_1(D, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_finset_1)).
% 6.29/2.31  tff(f_63, axiom, (![A, B, C]: ~((v1_finset_1(A) & r1_tarski(A, k2_zfmisc_1(B, C))) & (![D, E]: ~((((v1_finset_1(D) & r1_tarski(D, B)) & v1_finset_1(E)) & r1_tarski(E, C)) & r1_tarski(A, k2_zfmisc_1(D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_finset_1)).
% 6.29/2.31  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.29/2.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.29/2.31  tff(f_36, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.29/2.31  tff(f_46, axiom, (![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 6.29/2.31  tff(c_28, plain, (v1_finset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.29/2.31  tff(c_26, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.29/2.31  tff(c_369, plain, (![A_65, B_66, C_67]: (v1_finset_1('#skF_2'(A_65, B_66, C_67)) | ~r1_tarski(A_65, k2_zfmisc_1(B_66, C_67)) | ~v1_finset_1(A_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.29/2.31  tff(c_376, plain, (v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_369])).
% 6.29/2.31  tff(c_380, plain, (v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_376])).
% 6.29/2.31  tff(c_863, plain, (![A_100, B_101, C_102]: (r1_tarski('#skF_2'(A_100, B_101, C_102), B_101) | ~r1_tarski(A_100, k2_zfmisc_1(B_101, C_102)) | ~v1_finset_1(A_100))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.29/2.31  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.29/2.31  tff(c_1503, plain, (![A_135, B_136, C_137]: (k2_xboole_0('#skF_2'(A_135, B_136, C_137), B_136)=B_136 | ~r1_tarski(A_135, k2_zfmisc_1(B_136, C_137)) | ~v1_finset_1(A_135))), inference(resolution, [status(thm)], [c_863, c_10])).
% 6.29/2.31  tff(c_1523, plain, (k2_xboole_0('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')='#skF_5' | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1503])).
% 6.29/2.31  tff(c_1535, plain, (k2_xboole_0('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1523])).
% 6.29/2.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.29/2.31  tff(c_36, plain, (![A_31, B_32]: (~r2_hidden('#skF_1'(A_31, B_32), B_32) | r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.29/2.31  tff(c_42, plain, (![A_33]: (r1_tarski(A_33, A_33))), inference(resolution, [status(thm)], [c_6, c_36])).
% 6.29/2.31  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(k2_xboole_0(A_6, B_7), C_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.29/2.31  tff(c_50, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_42, c_8])).
% 6.29/2.31  tff(c_1578, plain, (r1_tarski('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1535, c_50])).
% 6.29/2.31  tff(c_14, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_zfmisc_1('#skF_2'(A_17, B_18, C_19), '#skF_3'(A_17, B_18, C_19))) | ~r1_tarski(A_17, k2_zfmisc_1(B_18, C_19)) | ~v1_finset_1(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.29/2.31  tff(c_720, plain, (![A_88, B_89, C_90]: (r1_tarski('#skF_3'(A_88, B_89, C_90), C_90) | ~r1_tarski(A_88, k2_zfmisc_1(B_89, C_90)) | ~v1_finset_1(A_88))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.29/2.31  tff(c_1199, plain, (![A_123, B_124, C_125]: (k2_xboole_0('#skF_3'(A_123, B_124, C_125), C_125)=C_125 | ~r1_tarski(A_123, k2_zfmisc_1(B_124, C_125)) | ~v1_finset_1(A_123))), inference(resolution, [status(thm)], [c_720, c_10])).
% 6.29/2.31  tff(c_1214, plain, (k2_xboole_0('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_6')='#skF_6' | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1199])).
% 6.29/2.31  tff(c_1222, plain, (k2_xboole_0('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1214])).
% 6.29/2.31  tff(c_51, plain, (![A_33]: (k2_xboole_0(A_33, A_33)=A_33)), inference(resolution, [status(thm)], [c_42, c_10])).
% 6.29/2.31  tff(c_41, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_36])).
% 6.29/2.31  tff(c_1116, plain, (![A_119, F_117, E_122, D_121, B_120, C_118]: (r1_tarski(k2_xboole_0(A_119, B_120), k2_zfmisc_1(k2_xboole_0(C_118, E_122), k2_xboole_0(D_121, F_117))) | ~r1_tarski(B_120, k2_zfmisc_1(E_122, F_117)) | ~r1_tarski(A_119, k2_zfmisc_1(C_118, D_121)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.29/2.31  tff(c_2561, plain, (![E_174, D_176, A_175, C_172, B_173, F_171]: (r1_tarski(A_175, k2_zfmisc_1(k2_xboole_0(C_172, E_174), k2_xboole_0(D_176, F_171))) | ~r1_tarski(B_173, k2_zfmisc_1(E_174, F_171)) | ~r1_tarski(A_175, k2_zfmisc_1(C_172, D_176)))), inference(resolution, [status(thm)], [c_1116, c_8])).
% 6.29/2.31  tff(c_4863, plain, (![E_266, A_267, F_268, C_270, D_269]: (r1_tarski(A_267, k2_zfmisc_1(k2_xboole_0(C_270, E_266), k2_xboole_0(D_269, F_268))) | ~r1_tarski(A_267, k2_zfmisc_1(C_270, D_269)))), inference(resolution, [status(thm)], [c_41, c_2561])).
% 6.29/2.31  tff(c_5032, plain, (![A_271, A_272, D_273, F_274]: (r1_tarski(A_271, k2_zfmisc_1(A_272, k2_xboole_0(D_273, F_274))) | ~r1_tarski(A_271, k2_zfmisc_1(A_272, D_273)))), inference(superposition, [status(thm), theory('equality')], [c_51, c_4863])).
% 6.29/2.31  tff(c_5527, plain, (![A_289, A_290]: (r1_tarski(A_289, k2_zfmisc_1(A_290, '#skF_6')) | ~r1_tarski(A_289, k2_zfmisc_1(A_290, '#skF_3'('#skF_4', '#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_1222, c_5032])).
% 6.29/2.31  tff(c_5563, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_6')) | ~r1_tarski('#skF_4', k2_zfmisc_1('#skF_5', '#skF_6')) | ~v1_finset_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_5527])).
% 6.29/2.31  tff(c_5586, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_5563])).
% 6.29/2.31  tff(c_24, plain, (![D_23]: (~r1_tarski('#skF_4', k2_zfmisc_1(D_23, '#skF_6')) | ~r1_tarski(D_23, '#skF_5') | ~v1_finset_1(D_23))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.29/2.31  tff(c_5612, plain, (~r1_tarski('#skF_2'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | ~v1_finset_1('#skF_2'('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_5586, c_24])).
% 6.29/2.31  tff(c_5637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_380, c_1578, c_5612])).
% 6.29/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.31  
% 6.29/2.31  Inference rules
% 6.29/2.31  ----------------------
% 6.29/2.31  #Ref     : 0
% 6.29/2.31  #Sup     : 1408
% 6.29/2.31  #Fact    : 0
% 6.29/2.31  #Define  : 0
% 6.29/2.31  #Split   : 4
% 6.29/2.31  #Chain   : 0
% 6.29/2.31  #Close   : 0
% 6.29/2.31  
% 6.29/2.31  Ordering : KBO
% 6.29/2.31  
% 6.29/2.31  Simplification rules
% 6.29/2.31  ----------------------
% 6.29/2.31  #Subsume      : 141
% 6.29/2.31  #Demod        : 401
% 6.29/2.31  #Tautology    : 264
% 6.29/2.31  #SimpNegUnit  : 0
% 6.29/2.31  #BackRed      : 0
% 6.29/2.31  
% 6.29/2.31  #Partial instantiations: 0
% 6.29/2.31  #Strategies tried      : 1
% 6.29/2.31  
% 6.29/2.31  Timing (in seconds)
% 6.29/2.31  ----------------------
% 6.29/2.32  Preprocessing        : 0.29
% 6.29/2.32  Parsing              : 0.16
% 6.29/2.32  CNF conversion       : 0.02
% 6.29/2.32  Main loop            : 1.26
% 6.29/2.32  Inferencing          : 0.39
% 6.29/2.32  Reduction            : 0.45
% 6.29/2.32  Demodulation         : 0.35
% 6.29/2.32  BG Simplification    : 0.04
% 6.29/2.32  Subsumption          : 0.29
% 6.29/2.32  Abstraction          : 0.05
% 6.29/2.32  MUC search           : 0.00
% 6.29/2.32  Cooper               : 0.00
% 6.29/2.32  Total                : 1.59
% 6.29/2.32  Index Insertion      : 0.00
% 6.29/2.32  Index Deletion       : 0.00
% 6.29/2.32  Index Matching       : 0.00
% 6.29/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
