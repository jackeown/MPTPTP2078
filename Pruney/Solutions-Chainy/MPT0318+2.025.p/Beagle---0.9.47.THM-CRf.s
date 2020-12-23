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
% DateTime   : Thu Dec  3 09:54:05 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 ( 140 expanded)
%              Number of equality atoms :   20 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_39,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_39])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_38])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_71,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = '#skF_2'
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_43,c_36])).

tff(c_72,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_101,plain,(
    ! [C_63,B_64,D_65] :
      ( r2_hidden(k4_tarski(C_63,B_64),k2_zfmisc_1(k1_tarski(C_63),D_65))
      | ~ r2_hidden(B_64,D_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,(
    ! [B_69] :
      ( r2_hidden(k4_tarski('#skF_4',B_69),'#skF_2')
      | ~ r2_hidden(B_69,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_101])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_136,plain,(
    ! [B_69] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(B_69,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_130,c_2])).

tff(c_142,plain,(
    ! [B_70] : ~ r2_hidden(B_70,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_147,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_6])).

tff(c_150,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_147,c_44])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_150])).

tff(c_155,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_244,plain,(
    ! [A_101,D_102,C_103] :
      ( r2_hidden(k4_tarski(A_101,D_102),k2_zfmisc_1(C_103,k1_tarski(D_102)))
      | ~ r2_hidden(A_101,C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_262,plain,(
    ! [C_104,D_105,A_106] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_104,k1_tarski(D_105)))
      | ~ r2_hidden(A_106,C_104) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_264,plain,(
    ! [A_106] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_106,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_262])).

tff(c_267,plain,(
    ! [A_107] : ~ r2_hidden(A_107,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_264])).

tff(c_272,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_267])).

tff(c_275,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_272,c_44])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  %$ r2_hidden > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.02/1.30  
% 2.02/1.30  %Foreground sorts:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Background operators:
% 2.02/1.30  
% 2.02/1.30  
% 2.02/1.30  %Foreground operators:
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.30  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.02/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.30  
% 2.02/1.31  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.02/1.31  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.31  tff(f_73, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.02/1.31  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.02/1.31  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 2.02/1.31  tff(f_63, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.02/1.31  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.02/1.31  tff(c_39, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.31  tff(c_43, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_39])).
% 2.02/1.31  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.31  tff(c_45, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_38])).
% 2.02/1.31  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.31  tff(c_36, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.02/1.31  tff(c_71, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))='#skF_2' | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_43, c_43, c_36])).
% 2.02/1.31  tff(c_72, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')='#skF_2'), inference(splitLeft, [status(thm)], [c_71])).
% 2.02/1.31  tff(c_101, plain, (![C_63, B_64, D_65]: (r2_hidden(k4_tarski(C_63, B_64), k2_zfmisc_1(k1_tarski(C_63), D_65)) | ~r2_hidden(B_64, D_65))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.31  tff(c_130, plain, (![B_69]: (r2_hidden(k4_tarski('#skF_4', B_69), '#skF_2') | ~r2_hidden(B_69, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_101])).
% 2.02/1.31  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.31  tff(c_136, plain, (![B_69]: (~v1_xboole_0('#skF_2') | ~r2_hidden(B_69, '#skF_3'))), inference(resolution, [status(thm)], [c_130, c_2])).
% 2.02/1.31  tff(c_142, plain, (![B_70]: (~r2_hidden(B_70, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_136])).
% 2.02/1.31  tff(c_147, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_142])).
% 2.02/1.31  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.31  tff(c_44, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_6])).
% 2.02/1.31  tff(c_150, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_147, c_44])).
% 2.02/1.31  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_150])).
% 2.02/1.31  tff(c_155, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))='#skF_2'), inference(splitRight, [status(thm)], [c_71])).
% 2.02/1.31  tff(c_244, plain, (![A_101, D_102, C_103]: (r2_hidden(k4_tarski(A_101, D_102), k2_zfmisc_1(C_103, k1_tarski(D_102))) | ~r2_hidden(A_101, C_103))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.31  tff(c_262, plain, (![C_104, D_105, A_106]: (~v1_xboole_0(k2_zfmisc_1(C_104, k1_tarski(D_105))) | ~r2_hidden(A_106, C_104))), inference(resolution, [status(thm)], [c_244, c_2])).
% 2.02/1.31  tff(c_264, plain, (![A_106]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_106, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_155, c_262])).
% 2.02/1.31  tff(c_267, plain, (![A_107]: (~r2_hidden(A_107, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_264])).
% 2.02/1.31  tff(c_272, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_267])).
% 2.02/1.31  tff(c_275, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_272, c_44])).
% 2.02/1.31  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_275])).
% 2.02/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  Inference rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Ref     : 0
% 2.02/1.31  #Sup     : 50
% 2.02/1.31  #Fact    : 0
% 2.02/1.31  #Define  : 0
% 2.02/1.31  #Split   : 1
% 2.02/1.31  #Chain   : 0
% 2.02/1.31  #Close   : 0
% 2.02/1.31  
% 2.02/1.31  Ordering : KBO
% 2.02/1.31  
% 2.02/1.31  Simplification rules
% 2.02/1.31  ----------------------
% 2.02/1.31  #Subsume      : 4
% 2.02/1.31  #Demod        : 6
% 2.02/1.31  #Tautology    : 27
% 2.02/1.31  #SimpNegUnit  : 2
% 2.02/1.31  #BackRed      : 2
% 2.02/1.31  
% 2.02/1.31  #Partial instantiations: 0
% 2.02/1.31  #Strategies tried      : 1
% 2.02/1.31  
% 2.02/1.31  Timing (in seconds)
% 2.02/1.31  ----------------------
% 2.02/1.31  Preprocessing        : 0.31
% 2.02/1.31  Parsing              : 0.17
% 2.02/1.31  CNF conversion       : 0.02
% 2.02/1.31  Main loop            : 0.18
% 2.02/1.31  Inferencing          : 0.07
% 2.02/1.31  Reduction            : 0.05
% 2.02/1.31  Demodulation         : 0.03
% 2.02/1.31  BG Simplification    : 0.01
% 2.02/1.31  Subsumption          : 0.03
% 2.02/1.31  Abstraction          : 0.01
% 2.02/1.31  MUC search           : 0.00
% 2.02/1.31  Cooper               : 0.00
% 2.02/1.31  Total                : 0.52
% 2.02/1.31  Index Insertion      : 0.00
% 2.02/1.31  Index Deletion       : 0.00
% 2.02/1.31  Index Matching       : 0.00
% 2.02/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
