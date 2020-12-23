%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:14 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 125 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 224 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
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

tff(c_36,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,(
    ! [B_122,A_123] :
      ( v1_relat_1(B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(A_124)
      | ~ v1_relat_1(B_125)
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_97,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_98,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_38])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_479,plain,(
    ! [A_191,B_192,C_193] :
      ( r2_hidden(k4_tarski('#skF_2'(A_191,B_192,C_193),'#skF_4'(A_191,B_192,C_193)),A_191)
      | r2_hidden(k4_tarski('#skF_5'(A_191,B_192,C_193),'#skF_6'(A_191,B_192,C_193)),C_193)
      | k5_relat_1(A_191,B_192) = C_193
      | ~ v1_relat_1(C_193)
      | ~ v1_relat_1(B_192)
      | ~ v1_relat_1(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_113,B_114] : ~ r2_hidden(A_113,k2_zfmisc_1(A_113,B_114)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_62])).

tff(c_537,plain,(
    ! [A_191,B_192] :
      ( r2_hidden(k4_tarski('#skF_2'(A_191,B_192,k1_xboole_0),'#skF_4'(A_191,B_192,k1_xboole_0)),A_191)
      | k5_relat_1(A_191,B_192) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_192)
      | ~ v1_relat_1(A_191) ) ),
    inference(resolution,[status(thm)],[c_479,c_65])).

tff(c_555,plain,(
    ! [A_194,B_195] :
      ( r2_hidden(k4_tarski('#skF_2'(A_194,B_195,k1_xboole_0),'#skF_4'(A_194,B_195,k1_xboole_0)),A_194)
      | k5_relat_1(A_194,B_195) = k1_xboole_0
      | ~ v1_relat_1(B_195)
      | ~ v1_relat_1(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_537])).

tff(c_585,plain,(
    ! [B_195] :
      ( k5_relat_1(k1_xboole_0,B_195) = k1_xboole_0
      | ~ v1_relat_1(B_195)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_555,c_65])).

tff(c_596,plain,(
    ! [B_196] :
      ( k5_relat_1(k1_xboole_0,B_196) = k1_xboole_0
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_585])).

tff(c_602,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_596])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_602])).

tff(c_609,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_626,plain,(
    ! [B_199,A_200] :
      ( v1_relat_1(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_200))
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_631,plain,(
    ! [A_201,B_202] :
      ( v1_relat_1(A_201)
      | ~ v1_relat_1(B_202)
      | ~ r1_tarski(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_14,c_626])).

tff(c_635,plain,(
    ! [A_1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_631])).

tff(c_636,plain,(
    ! [A_1] : ~ v1_relat_1(A_1) ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_636,c_38])).

tff(c_641,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_708,plain,(
    ! [A_223,B_224,C_225] :
      ( r2_hidden(k4_tarski('#skF_4'(A_223,B_224,C_225),'#skF_3'(A_223,B_224,C_225)),B_224)
      | r2_hidden(k4_tarski('#skF_5'(A_223,B_224,C_225),'#skF_6'(A_223,B_224,C_225)),C_225)
      | k5_relat_1(A_223,B_224) = C_225
      | ~ v1_relat_1(C_225)
      | ~ v1_relat_1(B_224)
      | ~ v1_relat_1(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_722,plain,(
    ! [A_223,C_225] :
      ( r2_hidden(k4_tarski('#skF_5'(A_223,k1_xboole_0,C_225),'#skF_6'(A_223,k1_xboole_0,C_225)),C_225)
      | k5_relat_1(A_223,k1_xboole_0) = C_225
      | ~ v1_relat_1(C_225)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_223) ) ),
    inference(resolution,[status(thm)],[c_708,c_65])).

tff(c_765,plain,(
    ! [A_229,C_230] :
      ( r2_hidden(k4_tarski('#skF_5'(A_229,k1_xboole_0,C_230),'#skF_6'(A_229,k1_xboole_0,C_230)),C_230)
      | k5_relat_1(A_229,k1_xboole_0) = C_230
      | ~ v1_relat_1(C_230)
      | ~ v1_relat_1(A_229) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_722])).

tff(c_783,plain,(
    ! [A_229] :
      ( k5_relat_1(A_229,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_229) ) ),
    inference(resolution,[status(thm)],[c_765,c_65])).

tff(c_791,plain,(
    ! [A_231] :
      ( k5_relat_1(A_231,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_783])).

tff(c_797,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_791])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_609,c_797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  
% 3.10/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3
% 3.10/1.48  
% 3.10/1.48  %Foreground sorts:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Background operators:
% 3.10/1.48  
% 3.10/1.48  
% 3.10/1.48  %Foreground operators:
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.48  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.10/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.10/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.10/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.10/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.10/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.10/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.10/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.10/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.48  
% 3.10/1.50  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.10/1.50  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.10/1.50  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.50  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.10/1.50  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.10/1.50  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.10/1.50  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.10/1.50  tff(c_36, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.10/1.50  tff(c_76, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 3.10/1.50  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.10/1.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.50  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.10/1.50  tff(c_88, plain, (![B_122, A_123]: (v1_relat_1(B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_123)) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.10/1.50  tff(c_93, plain, (![A_124, B_125]: (v1_relat_1(A_124) | ~v1_relat_1(B_125) | ~r1_tarski(A_124, B_125))), inference(resolution, [status(thm)], [c_14, c_88])).
% 3.10/1.50  tff(c_97, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_93])).
% 3.10/1.50  tff(c_98, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_97])).
% 3.10/1.50  tff(c_103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_38])).
% 3.10/1.50  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_97])).
% 3.10/1.50  tff(c_479, plain, (![A_191, B_192, C_193]: (r2_hidden(k4_tarski('#skF_2'(A_191, B_192, C_193), '#skF_4'(A_191, B_192, C_193)), A_191) | r2_hidden(k4_tarski('#skF_5'(A_191, B_192, C_193), '#skF_6'(A_191, B_192, C_193)), C_193) | k5_relat_1(A_191, B_192)=C_193 | ~v1_relat_1(C_193) | ~v1_relat_1(B_192) | ~v1_relat_1(A_191))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.10/1.50  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.50  tff(c_62, plain, (![A_113, B_114]: (~r2_hidden(A_113, k2_zfmisc_1(A_113, B_114)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.50  tff(c_65, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_62])).
% 3.10/1.50  tff(c_537, plain, (![A_191, B_192]: (r2_hidden(k4_tarski('#skF_2'(A_191, B_192, k1_xboole_0), '#skF_4'(A_191, B_192, k1_xboole_0)), A_191) | k5_relat_1(A_191, B_192)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_192) | ~v1_relat_1(A_191))), inference(resolution, [status(thm)], [c_479, c_65])).
% 3.10/1.50  tff(c_555, plain, (![A_194, B_195]: (r2_hidden(k4_tarski('#skF_2'(A_194, B_195, k1_xboole_0), '#skF_4'(A_194, B_195, k1_xboole_0)), A_194) | k5_relat_1(A_194, B_195)=k1_xboole_0 | ~v1_relat_1(B_195) | ~v1_relat_1(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_537])).
% 3.10/1.50  tff(c_585, plain, (![B_195]: (k5_relat_1(k1_xboole_0, B_195)=k1_xboole_0 | ~v1_relat_1(B_195) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_555, c_65])).
% 3.10/1.50  tff(c_596, plain, (![B_196]: (k5_relat_1(k1_xboole_0, B_196)=k1_xboole_0 | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_585])).
% 3.10/1.50  tff(c_602, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_596])).
% 3.10/1.50  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_602])).
% 3.10/1.50  tff(c_609, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 3.10/1.50  tff(c_626, plain, (![B_199, A_200]: (v1_relat_1(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_200)) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.10/1.50  tff(c_631, plain, (![A_201, B_202]: (v1_relat_1(A_201) | ~v1_relat_1(B_202) | ~r1_tarski(A_201, B_202))), inference(resolution, [status(thm)], [c_14, c_626])).
% 3.10/1.50  tff(c_635, plain, (![A_1]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_631])).
% 3.10/1.50  tff(c_636, plain, (![A_1]: (~v1_relat_1(A_1))), inference(splitLeft, [status(thm)], [c_635])).
% 3.10/1.50  tff(c_640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_636, c_38])).
% 3.10/1.50  tff(c_641, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_635])).
% 3.10/1.50  tff(c_708, plain, (![A_223, B_224, C_225]: (r2_hidden(k4_tarski('#skF_4'(A_223, B_224, C_225), '#skF_3'(A_223, B_224, C_225)), B_224) | r2_hidden(k4_tarski('#skF_5'(A_223, B_224, C_225), '#skF_6'(A_223, B_224, C_225)), C_225) | k5_relat_1(A_223, B_224)=C_225 | ~v1_relat_1(C_225) | ~v1_relat_1(B_224) | ~v1_relat_1(A_223))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.10/1.50  tff(c_722, plain, (![A_223, C_225]: (r2_hidden(k4_tarski('#skF_5'(A_223, k1_xboole_0, C_225), '#skF_6'(A_223, k1_xboole_0, C_225)), C_225) | k5_relat_1(A_223, k1_xboole_0)=C_225 | ~v1_relat_1(C_225) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_223))), inference(resolution, [status(thm)], [c_708, c_65])).
% 3.10/1.50  tff(c_765, plain, (![A_229, C_230]: (r2_hidden(k4_tarski('#skF_5'(A_229, k1_xboole_0, C_230), '#skF_6'(A_229, k1_xboole_0, C_230)), C_230) | k5_relat_1(A_229, k1_xboole_0)=C_230 | ~v1_relat_1(C_230) | ~v1_relat_1(A_229))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_722])).
% 3.10/1.50  tff(c_783, plain, (![A_229]: (k5_relat_1(A_229, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_229))), inference(resolution, [status(thm)], [c_765, c_65])).
% 3.10/1.50  tff(c_791, plain, (![A_231]: (k5_relat_1(A_231, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_641, c_783])).
% 3.10/1.50  tff(c_797, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_791])).
% 3.10/1.50  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_609, c_797])).
% 3.10/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  Inference rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Ref     : 0
% 3.10/1.50  #Sup     : 149
% 3.10/1.50  #Fact    : 0
% 3.10/1.50  #Define  : 0
% 3.10/1.50  #Split   : 3
% 3.10/1.50  #Chain   : 0
% 3.10/1.50  #Close   : 0
% 3.10/1.50  
% 3.10/1.50  Ordering : KBO
% 3.10/1.50  
% 3.10/1.50  Simplification rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Subsume      : 39
% 3.10/1.50  #Demod        : 115
% 3.10/1.50  #Tautology    : 18
% 3.10/1.50  #SimpNegUnit  : 12
% 3.10/1.50  #BackRed      : 2
% 3.10/1.50  
% 3.10/1.50  #Partial instantiations: 0
% 3.10/1.50  #Strategies tried      : 1
% 3.10/1.50  
% 3.10/1.50  Timing (in seconds)
% 3.10/1.50  ----------------------
% 3.10/1.50  Preprocessing        : 0.31
% 3.10/1.50  Parsing              : 0.16
% 3.10/1.50  CNF conversion       : 0.04
% 3.10/1.50  Main loop            : 0.42
% 3.10/1.50  Inferencing          : 0.15
% 3.10/1.50  Reduction            : 0.10
% 3.10/1.50  Demodulation         : 0.06
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.12
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.77
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
