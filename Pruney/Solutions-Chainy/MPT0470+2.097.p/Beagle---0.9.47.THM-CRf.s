%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 106 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   82 ( 182 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_34,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_84,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [B_119,A_120] :
      ( v1_relat_1(B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_120))
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_83,plain,(
    ! [A_5] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_85,plain,(
    ! [A_5] : ~ v1_relat_1(A_5) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_36])).

tff(c_89,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_183,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden(k4_tarski('#skF_2'(A_159,B_160,C_161),'#skF_4'(A_159,B_160,C_161)),A_159)
      | r2_hidden(k4_tarski('#skF_5'(A_159,B_160,C_161),'#skF_6'(A_159,B_160,C_161)),C_161)
      | k5_relat_1(A_159,B_160) = C_161
      | ~ v1_relat_1(C_161)
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_114,B_115] : ~ r2_hidden(A_114,k2_zfmisc_1(A_114,B_115)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_63,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_241,plain,(
    ! [A_159,B_160] :
      ( r2_hidden(k4_tarski('#skF_2'(A_159,B_160,k1_xboole_0),'#skF_4'(A_159,B_160,k1_xboole_0)),A_159)
      | k5_relat_1(A_159,B_160) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_160)
      | ~ v1_relat_1(A_159) ) ),
    inference(resolution,[status(thm)],[c_183,c_63])).

tff(c_300,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_2'(A_165,B_166,k1_xboole_0),'#skF_4'(A_165,B_166,k1_xboole_0)),A_165)
      | k5_relat_1(A_165,B_166) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_241])).

tff(c_330,plain,(
    ! [B_166] :
      ( k5_relat_1(k1_xboole_0,B_166) = k1_xboole_0
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_300,c_63])).

tff(c_341,plain,(
    ! [B_167] :
      ( k5_relat_1(k1_xboole_0,B_167) = k1_xboole_0
      | ~ v1_relat_1(B_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_330])).

tff(c_347,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_341])).

tff(c_352,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_347])).

tff(c_353,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_359,plain,(
    ! [A_5] : ~ v1_relat_1(A_5) ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_36])).

tff(c_363,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_600,plain,(
    ! [A_212,B_213,C_214] :
      ( r2_hidden(k4_tarski('#skF_4'(A_212,B_213,C_214),'#skF_3'(A_212,B_213,C_214)),B_213)
      | r2_hidden(k4_tarski('#skF_5'(A_212,B_213,C_214),'#skF_6'(A_212,B_213,C_214)),C_214)
      | k5_relat_1(A_212,B_213) = C_214
      | ~ v1_relat_1(C_214)
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_630,plain,(
    ! [A_212,C_214] :
      ( r2_hidden(k4_tarski('#skF_5'(A_212,k1_xboole_0,C_214),'#skF_6'(A_212,k1_xboole_0,C_214)),C_214)
      | k5_relat_1(A_212,k1_xboole_0) = C_214
      | ~ v1_relat_1(C_214)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_600,c_63])).

tff(c_801,plain,(
    ! [A_226,C_227] :
      ( r2_hidden(k4_tarski('#skF_5'(A_226,k1_xboole_0,C_227),'#skF_6'(A_226,k1_xboole_0,C_227)),C_227)
      | k5_relat_1(A_226,k1_xboole_0) = C_227
      | ~ v1_relat_1(C_227)
      | ~ v1_relat_1(A_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_630])).

tff(c_834,plain,(
    ! [A_226] :
      ( k5_relat_1(A_226,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_226) ) ),
    inference(resolution,[status(thm)],[c_801,c_63])).

tff(c_848,plain,(
    ! [A_228] :
      ( k5_relat_1(A_228,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_834])).

tff(c_854,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_848])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  
% 3.25/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.51  %$ r2_hidden > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3
% 3.25/1.51  
% 3.25/1.51  %Foreground sorts:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Background operators:
% 3.25/1.51  
% 3.25/1.51  
% 3.25/1.51  %Foreground operators:
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.51  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.25/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.25/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.25/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.25/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.51  
% 3.46/1.52  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 3.46/1.52  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.46/1.52  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.46/1.52  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 3.46/1.52  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.46/1.52  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.46/1.52  tff(c_34, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.52  tff(c_84, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.46/1.52  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.46/1.52  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.46/1.52  tff(c_79, plain, (![B_119, A_120]: (v1_relat_1(B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_120)) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.52  tff(c_83, plain, (![A_5]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_10, c_79])).
% 3.46/1.52  tff(c_85, plain, (![A_5]: (~v1_relat_1(A_5))), inference(splitLeft, [status(thm)], [c_83])).
% 3.46/1.52  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_36])).
% 3.46/1.52  tff(c_89, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 3.46/1.52  tff(c_183, plain, (![A_159, B_160, C_161]: (r2_hidden(k4_tarski('#skF_2'(A_159, B_160, C_161), '#skF_4'(A_159, B_160, C_161)), A_159) | r2_hidden(k4_tarski('#skF_5'(A_159, B_160, C_161), '#skF_6'(A_159, B_160, C_161)), C_161) | k5_relat_1(A_159, B_160)=C_161 | ~v1_relat_1(C_161) | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.52  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.52  tff(c_60, plain, (![A_114, B_115]: (~r2_hidden(A_114, k2_zfmisc_1(A_114, B_115)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.46/1.52  tff(c_63, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_60])).
% 3.46/1.52  tff(c_241, plain, (![A_159, B_160]: (r2_hidden(k4_tarski('#skF_2'(A_159, B_160, k1_xboole_0), '#skF_4'(A_159, B_160, k1_xboole_0)), A_159) | k5_relat_1(A_159, B_160)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_160) | ~v1_relat_1(A_159))), inference(resolution, [status(thm)], [c_183, c_63])).
% 3.46/1.52  tff(c_300, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_2'(A_165, B_166, k1_xboole_0), '#skF_4'(A_165, B_166, k1_xboole_0)), A_165) | k5_relat_1(A_165, B_166)=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_241])).
% 3.46/1.52  tff(c_330, plain, (![B_166]: (k5_relat_1(k1_xboole_0, B_166)=k1_xboole_0 | ~v1_relat_1(B_166) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_300, c_63])).
% 3.46/1.52  tff(c_341, plain, (![B_167]: (k5_relat_1(k1_xboole_0, B_167)=k1_xboole_0 | ~v1_relat_1(B_167))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_330])).
% 3.46/1.52  tff(c_347, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_341])).
% 3.46/1.52  tff(c_352, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_347])).
% 3.46/1.52  tff(c_353, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.46/1.52  tff(c_359, plain, (![A_5]: (~v1_relat_1(A_5))), inference(splitLeft, [status(thm)], [c_83])).
% 3.46/1.52  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_36])).
% 3.46/1.52  tff(c_363, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_83])).
% 3.46/1.52  tff(c_600, plain, (![A_212, B_213, C_214]: (r2_hidden(k4_tarski('#skF_4'(A_212, B_213, C_214), '#skF_3'(A_212, B_213, C_214)), B_213) | r2_hidden(k4_tarski('#skF_5'(A_212, B_213, C_214), '#skF_6'(A_212, B_213, C_214)), C_214) | k5_relat_1(A_212, B_213)=C_214 | ~v1_relat_1(C_214) | ~v1_relat_1(B_213) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.52  tff(c_630, plain, (![A_212, C_214]: (r2_hidden(k4_tarski('#skF_5'(A_212, k1_xboole_0, C_214), '#skF_6'(A_212, k1_xboole_0, C_214)), C_214) | k5_relat_1(A_212, k1_xboole_0)=C_214 | ~v1_relat_1(C_214) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_600, c_63])).
% 3.46/1.52  tff(c_801, plain, (![A_226, C_227]: (r2_hidden(k4_tarski('#skF_5'(A_226, k1_xboole_0, C_227), '#skF_6'(A_226, k1_xboole_0, C_227)), C_227) | k5_relat_1(A_226, k1_xboole_0)=C_227 | ~v1_relat_1(C_227) | ~v1_relat_1(A_226))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_630])).
% 3.46/1.52  tff(c_834, plain, (![A_226]: (k5_relat_1(A_226, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_226))), inference(resolution, [status(thm)], [c_801, c_63])).
% 3.46/1.52  tff(c_848, plain, (![A_228]: (k5_relat_1(A_228, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_834])).
% 3.46/1.52  tff(c_854, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_848])).
% 3.46/1.52  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_854])).
% 3.46/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.52  
% 3.46/1.52  Inference rules
% 3.46/1.52  ----------------------
% 3.46/1.52  #Ref     : 0
% 3.46/1.52  #Sup     : 160
% 3.46/1.52  #Fact    : 0
% 3.46/1.52  #Define  : 0
% 3.46/1.52  #Split   : 3
% 3.46/1.52  #Chain   : 0
% 3.46/1.52  #Close   : 0
% 3.46/1.52  
% 3.46/1.52  Ordering : KBO
% 3.46/1.52  
% 3.46/1.52  Simplification rules
% 3.46/1.52  ----------------------
% 3.46/1.52  #Subsume      : 35
% 3.46/1.52  #Demod        : 77
% 3.46/1.52  #Tautology    : 14
% 3.46/1.52  #SimpNegUnit  : 9
% 3.46/1.52  #BackRed      : 2
% 3.46/1.52  
% 3.46/1.52  #Partial instantiations: 0
% 3.46/1.52  #Strategies tried      : 1
% 3.46/1.52  
% 3.46/1.52  Timing (in seconds)
% 3.46/1.52  ----------------------
% 3.46/1.53  Preprocessing        : 0.30
% 3.46/1.53  Parsing              : 0.15
% 3.46/1.53  CNF conversion       : 0.03
% 3.46/1.53  Main loop            : 0.47
% 3.46/1.53  Inferencing          : 0.17
% 3.46/1.53  Reduction            : 0.11
% 3.46/1.53  Demodulation         : 0.07
% 3.46/1.53  BG Simplification    : 0.02
% 3.46/1.53  Subsumption          : 0.14
% 3.46/1.53  Abstraction          : 0.02
% 3.46/1.53  MUC search           : 0.00
% 3.46/1.53  Cooper               : 0.00
% 3.46/1.53  Total                : 0.80
% 3.46/1.53  Index Insertion      : 0.00
% 3.46/1.53  Index Deletion       : 0.00
% 3.46/1.53  Index Matching       : 0.00
% 3.46/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
