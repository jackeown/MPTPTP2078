%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:20 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   52 (  98 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 156 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_34,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_104,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_114,B_115] :
      ( v1_relat_1(k3_xboole_0(A_114,B_115))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_78,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_36])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_194,plain,(
    ! [A_156,B_157,C_158] :
      ( r2_hidden(k4_tarski('#skF_2'(A_156,B_157,C_158),'#skF_4'(A_156,B_157,C_158)),A_156)
      | r2_hidden(k4_tarski('#skF_5'(A_156,B_157,C_158),'#skF_6'(A_156,B_157,C_158)),C_158)
      | k5_relat_1(A_156,B_157) = C_158
      | ~ v1_relat_1(C_158)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_66,plain,(
    ! [A_112,B_113] : ~ r2_hidden(A_112,k2_zfmisc_1(A_112,B_113)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_252,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(k4_tarski('#skF_2'(A_156,B_157,k1_xboole_0),'#skF_4'(A_156,B_157,k1_xboole_0)),A_156)
      | k5_relat_1(A_156,B_157) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_157)
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_194,c_72])).

tff(c_270,plain,(
    ! [A_159,B_160] :
      ( r2_hidden(k4_tarski('#skF_2'(A_159,B_160,k1_xboole_0),'#skF_4'(A_159,B_160,k1_xboole_0)),A_159)
      | k5_relat_1(A_159,B_160) = k1_xboole_0
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_252])).

tff(c_300,plain,(
    ! [B_160] :
      ( k5_relat_1(k1_xboole_0,B_160) = k1_xboole_0
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_270,c_72])).

tff(c_311,plain,(
    ! [B_161] :
      ( k5_relat_1(k1_xboole_0,B_161) = k1_xboole_0
      | ~ v1_relat_1(B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_300])).

tff(c_320,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_311])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_320])).

tff(c_327,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_473,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_hidden(k4_tarski('#skF_4'(A_196,B_197,C_198),'#skF_3'(A_196,B_197,C_198)),B_197)
      | r2_hidden(k4_tarski('#skF_5'(A_196,B_197,C_198),'#skF_6'(A_196,B_197,C_198)),C_198)
      | k5_relat_1(A_196,B_197) = C_198
      | ~ v1_relat_1(C_198)
      | ~ v1_relat_1(B_197)
      | ~ v1_relat_1(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_499,plain,(
    ! [A_196,C_198] :
      ( r2_hidden(k4_tarski('#skF_5'(A_196,k1_xboole_0,C_198),'#skF_6'(A_196,k1_xboole_0,C_198)),C_198)
      | k5_relat_1(A_196,k1_xboole_0) = C_198
      | ~ v1_relat_1(C_198)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_196) ) ),
    inference(resolution,[status(thm)],[c_473,c_72])).

tff(c_539,plain,(
    ! [A_199,C_200] :
      ( r2_hidden(k4_tarski('#skF_5'(A_199,k1_xboole_0,C_200),'#skF_6'(A_199,k1_xboole_0,C_200)),C_200)
      | k5_relat_1(A_199,k1_xboole_0) = C_200
      | ~ v1_relat_1(C_200)
      | ~ v1_relat_1(A_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_499])).

tff(c_565,plain,(
    ! [A_199] :
      ( k5_relat_1(A_199,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_199) ) ),
    inference(resolution,[status(thm)],[c_539,c_72])).

tff(c_575,plain,(
    ! [A_201] :
      ( k5_relat_1(A_201,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_565])).

tff(c_584,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_575])).

tff(c_590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_584])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.84  
% 3.65/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.85  %$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3
% 3.65/1.85  
% 3.65/1.85  %Foreground sorts:
% 3.65/1.85  
% 3.65/1.85  
% 3.65/1.85  %Background operators:
% 3.65/1.85  
% 3.65/1.85  
% 3.65/1.85  %Foreground operators:
% 3.65/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.65/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.65/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.85  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.65/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.65/1.85  tff('#skF_7', type, '#skF_7': $i).
% 3.65/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.85  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.65/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.65/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.65/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.65/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.65/1.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.65/1.85  
% 3.65/1.87  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.65/1.87  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.65/1.87  tff(f_60, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.65/1.87  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.65/1.87  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.65/1.87  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.65/1.87  tff(c_34, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.65/1.87  tff(c_104, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.65/1.87  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.65/1.87  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.65/1.87  tff(c_73, plain, (![A_114, B_115]: (v1_relat_1(k3_xboole_0(A_114, B_115)) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.87  tff(c_76, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 3.65/1.87  tff(c_78, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_76])).
% 3.65/1.87  tff(c_82, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_36])).
% 3.65/1.87  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_76])).
% 3.65/1.87  tff(c_194, plain, (![A_156, B_157, C_158]: (r2_hidden(k4_tarski('#skF_2'(A_156, B_157, C_158), '#skF_4'(A_156, B_157, C_158)), A_156) | r2_hidden(k4_tarski('#skF_5'(A_156, B_157, C_158), '#skF_6'(A_156, B_157, C_158)), C_158) | k5_relat_1(A_156, B_157)=C_158 | ~v1_relat_1(C_158) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.65/1.87  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.65/1.87  tff(c_66, plain, (![A_112, B_113]: (~r2_hidden(A_112, k2_zfmisc_1(A_112, B_113)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.65/1.87  tff(c_72, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 3.65/1.87  tff(c_252, plain, (![A_156, B_157]: (r2_hidden(k4_tarski('#skF_2'(A_156, B_157, k1_xboole_0), '#skF_4'(A_156, B_157, k1_xboole_0)), A_156) | k5_relat_1(A_156, B_157)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_157) | ~v1_relat_1(A_156))), inference(resolution, [status(thm)], [c_194, c_72])).
% 3.65/1.87  tff(c_270, plain, (![A_159, B_160]: (r2_hidden(k4_tarski('#skF_2'(A_159, B_160, k1_xboole_0), '#skF_4'(A_159, B_160, k1_xboole_0)), A_159) | k5_relat_1(A_159, B_160)=k1_xboole_0 | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_252])).
% 3.65/1.87  tff(c_300, plain, (![B_160]: (k5_relat_1(k1_xboole_0, B_160)=k1_xboole_0 | ~v1_relat_1(B_160) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_270, c_72])).
% 3.65/1.87  tff(c_311, plain, (![B_161]: (k5_relat_1(k1_xboole_0, B_161)=k1_xboole_0 | ~v1_relat_1(B_161))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_300])).
% 3.65/1.87  tff(c_320, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_311])).
% 3.65/1.87  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_320])).
% 3.65/1.87  tff(c_327, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.65/1.87  tff(c_473, plain, (![A_196, B_197, C_198]: (r2_hidden(k4_tarski('#skF_4'(A_196, B_197, C_198), '#skF_3'(A_196, B_197, C_198)), B_197) | r2_hidden(k4_tarski('#skF_5'(A_196, B_197, C_198), '#skF_6'(A_196, B_197, C_198)), C_198) | k5_relat_1(A_196, B_197)=C_198 | ~v1_relat_1(C_198) | ~v1_relat_1(B_197) | ~v1_relat_1(A_196))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.65/1.87  tff(c_499, plain, (![A_196, C_198]: (r2_hidden(k4_tarski('#skF_5'(A_196, k1_xboole_0, C_198), '#skF_6'(A_196, k1_xboole_0, C_198)), C_198) | k5_relat_1(A_196, k1_xboole_0)=C_198 | ~v1_relat_1(C_198) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_196))), inference(resolution, [status(thm)], [c_473, c_72])).
% 3.65/1.87  tff(c_539, plain, (![A_199, C_200]: (r2_hidden(k4_tarski('#skF_5'(A_199, k1_xboole_0, C_200), '#skF_6'(A_199, k1_xboole_0, C_200)), C_200) | k5_relat_1(A_199, k1_xboole_0)=C_200 | ~v1_relat_1(C_200) | ~v1_relat_1(A_199))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_499])).
% 3.65/1.87  tff(c_565, plain, (![A_199]: (k5_relat_1(A_199, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_199))), inference(resolution, [status(thm)], [c_539, c_72])).
% 3.65/1.87  tff(c_575, plain, (![A_201]: (k5_relat_1(A_201, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_201))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_565])).
% 3.65/1.87  tff(c_584, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_575])).
% 3.65/1.87  tff(c_590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_584])).
% 3.65/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.87  
% 3.65/1.87  Inference rules
% 3.65/1.87  ----------------------
% 3.65/1.87  #Ref     : 0
% 3.65/1.87  #Sup     : 108
% 3.65/1.87  #Fact    : 0
% 3.65/1.87  #Define  : 0
% 3.65/1.87  #Split   : 3
% 3.65/1.87  #Chain   : 0
% 3.65/1.87  #Close   : 0
% 3.65/1.87  
% 3.65/1.87  Ordering : KBO
% 3.65/1.87  
% 3.65/1.87  Simplification rules
% 3.65/1.87  ----------------------
% 3.65/1.87  #Subsume      : 13
% 3.65/1.87  #Demod        : 30
% 3.65/1.87  #Tautology    : 14
% 3.65/1.87  #SimpNegUnit  : 5
% 3.65/1.87  #BackRed      : 1
% 3.65/1.87  
% 3.65/1.87  #Partial instantiations: 0
% 3.65/1.87  #Strategies tried      : 1
% 3.65/1.87  
% 3.65/1.87  Timing (in seconds)
% 3.65/1.87  ----------------------
% 3.65/1.87  Preprocessing        : 0.49
% 3.65/1.87  Parsing              : 0.25
% 3.65/1.87  CNF conversion       : 0.05
% 3.65/1.87  Main loop            : 0.56
% 3.65/1.87  Inferencing          : 0.21
% 3.65/1.87  Reduction            : 0.13
% 3.65/1.87  Demodulation         : 0.08
% 3.65/1.87  BG Simplification    : 0.03
% 3.65/1.87  Subsumption          : 0.14
% 3.65/1.87  Abstraction          : 0.03
% 3.65/1.87  MUC search           : 0.00
% 3.65/1.87  Cooper               : 0.00
% 3.65/1.87  Total                : 1.10
% 3.65/1.87  Index Insertion      : 0.00
% 3.65/1.87  Index Deletion       : 0.00
% 3.65/1.87  Index Matching       : 0.00
% 3.65/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
