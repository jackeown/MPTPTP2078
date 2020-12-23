%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   60 (  96 expanded)
%              Number of leaves         :   34 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 138 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_5 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_30,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_52,plain,(
    k10_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_210,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(k4_tarski('#skF_8'(A_138,B_139),'#skF_7'(A_138,B_139)),A_138)
      | r2_hidden('#skF_9'(A_138,B_139),B_139)
      | k2_relat_1(A_138) = B_139 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [B_93,A_94] :
      ( v1_relat_1(B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94))
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_71,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_54])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_108,C_109] :
      ( r2_hidden(k4_tarski('#skF_10'(A_108,k2_relat_1(A_108),C_109),C_109),A_108)
      | ~ r2_hidden(C_109,k2_relat_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_93,plain,(
    ! [C_109] :
      ( r2_hidden(k4_tarski('#skF_10'(k1_xboole_0,k1_xboole_0,C_109),C_109),k1_xboole_0)
      | ~ r2_hidden(C_109,k2_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_97,plain,(
    ! [C_109] :
      ( r2_hidden(k4_tarski('#skF_10'(k1_xboole_0,k1_xboole_0,C_109),C_109),k1_xboole_0)
      | ~ r2_hidden(C_109,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_93])).

tff(c_141,plain,(
    ! [C_118,D_119,B_120,A_121] :
      ( r2_hidden(k4_tarski(C_118,D_119),B_120)
      | ~ r2_hidden(k4_tarski(C_118,D_119),A_121)
      | ~ r1_tarski(A_121,B_120)
      | ~ v1_relat_1(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_145,plain,(
    ! [C_109,B_120] :
      ( r2_hidden(k4_tarski('#skF_10'(k1_xboole_0,k1_xboole_0,C_109),C_109),B_120)
      | ~ r1_tarski(k1_xboole_0,B_120)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(C_109,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_97,c_141])).

tff(c_160,plain,(
    ! [C_125,B_126] :
      ( r2_hidden(k4_tarski('#skF_10'(k1_xboole_0,k1_xboole_0,C_125),C_125),B_126)
      | ~ r2_hidden(C_125,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2,c_145])).

tff(c_4,plain,(
    ! [A_2,B_3] : ~ r2_hidden(A_2,k2_zfmisc_1(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_175,plain,(
    ! [C_125] : ~ r2_hidden(C_125,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_216,plain,(
    ! [B_139] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_139),B_139)
      | k2_relat_1(k1_xboole_0) = B_139 ) ),
    inference(resolution,[status(thm)],[c_210,c_175])).

tff(c_248,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_142),B_142)
      | k1_xboole_0 = B_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_216])).

tff(c_201,plain,(
    ! [A_135,B_136,D_137] :
      ( r2_hidden('#skF_4'(A_135,B_136,k10_relat_1(A_135,B_136),D_137),B_136)
      | ~ r2_hidden(D_137,k10_relat_1(A_135,B_136))
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_209,plain,(
    ! [D_137,A_135] :
      ( ~ r2_hidden(D_137,k10_relat_1(A_135,k1_xboole_0))
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_201,c_175])).

tff(c_263,plain,(
    ! [A_143] :
      ( ~ v1_relat_1(A_143)
      | k10_relat_1(A_143,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_248,c_209])).

tff(c_269,plain,(
    k10_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_263])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_269])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_2 > #skF_8 > #skF_4 > #skF_3 > #skF_7 > #skF_9 > #skF_5 > #skF_10
% 2.02/1.32  
% 2.02/1.32  %Foreground sorts:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Background operators:
% 2.02/1.32  
% 2.02/1.32  
% 2.02/1.32  %Foreground operators:
% 2.02/1.32  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.02/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.32  tff('#skF_11', type, '#skF_11': $i).
% 2.02/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.32  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.02/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.02/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.02/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.32  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.02/1.32  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 2.02/1.32  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.02/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.32  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 2.02/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.32  
% 2.02/1.33  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 2.02/1.33  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.02/1.33  tff(f_76, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.02/1.33  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.02/1.33  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.02/1.33  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.02/1.33  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 2.02/1.33  tff(f_30, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.02/1.33  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.02/1.33  tff(c_52, plain, (k10_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.33  tff(c_54, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.02/1.33  tff(c_48, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.02/1.33  tff(c_210, plain, (![A_138, B_139]: (r2_hidden(k4_tarski('#skF_8'(A_138, B_139), '#skF_7'(A_138, B_139)), A_138) | r2_hidden('#skF_9'(A_138, B_139), B_139) | k2_relat_1(A_138)=B_139)), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.33  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.02/1.33  tff(c_66, plain, (![B_93, A_94]: (v1_relat_1(B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.33  tff(c_70, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_6, c_66])).
% 2.02/1.33  tff(c_71, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_70])).
% 2.02/1.33  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_54])).
% 2.02/1.33  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_70])).
% 2.02/1.33  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.33  tff(c_84, plain, (![A_108, C_109]: (r2_hidden(k4_tarski('#skF_10'(A_108, k2_relat_1(A_108), C_109), C_109), A_108) | ~r2_hidden(C_109, k2_relat_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.02/1.33  tff(c_93, plain, (![C_109]: (r2_hidden(k4_tarski('#skF_10'(k1_xboole_0, k1_xboole_0, C_109), C_109), k1_xboole_0) | ~r2_hidden(C_109, k2_relat_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_84])).
% 2.02/1.33  tff(c_97, plain, (![C_109]: (r2_hidden(k4_tarski('#skF_10'(k1_xboole_0, k1_xboole_0, C_109), C_109), k1_xboole_0) | ~r2_hidden(C_109, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_93])).
% 2.02/1.33  tff(c_141, plain, (![C_118, D_119, B_120, A_121]: (r2_hidden(k4_tarski(C_118, D_119), B_120) | ~r2_hidden(k4_tarski(C_118, D_119), A_121) | ~r1_tarski(A_121, B_120) | ~v1_relat_1(A_121))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.33  tff(c_145, plain, (![C_109, B_120]: (r2_hidden(k4_tarski('#skF_10'(k1_xboole_0, k1_xboole_0, C_109), C_109), B_120) | ~r1_tarski(k1_xboole_0, B_120) | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(C_109, k1_xboole_0))), inference(resolution, [status(thm)], [c_97, c_141])).
% 2.02/1.33  tff(c_160, plain, (![C_125, B_126]: (r2_hidden(k4_tarski('#skF_10'(k1_xboole_0, k1_xboole_0, C_125), C_125), B_126) | ~r2_hidden(C_125, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2, c_145])).
% 2.02/1.33  tff(c_4, plain, (![A_2, B_3]: (~r2_hidden(A_2, k2_zfmisc_1(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.02/1.33  tff(c_175, plain, (![C_125]: (~r2_hidden(C_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_160, c_4])).
% 2.02/1.33  tff(c_216, plain, (![B_139]: (r2_hidden('#skF_9'(k1_xboole_0, B_139), B_139) | k2_relat_1(k1_xboole_0)=B_139)), inference(resolution, [status(thm)], [c_210, c_175])).
% 2.02/1.33  tff(c_248, plain, (![B_142]: (r2_hidden('#skF_9'(k1_xboole_0, B_142), B_142) | k1_xboole_0=B_142)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_216])).
% 2.02/1.33  tff(c_201, plain, (![A_135, B_136, D_137]: (r2_hidden('#skF_4'(A_135, B_136, k10_relat_1(A_135, B_136), D_137), B_136) | ~r2_hidden(D_137, k10_relat_1(A_135, B_136)) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.02/1.33  tff(c_209, plain, (![D_137, A_135]: (~r2_hidden(D_137, k10_relat_1(A_135, k1_xboole_0)) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_201, c_175])).
% 2.02/1.33  tff(c_263, plain, (![A_143]: (~v1_relat_1(A_143) | k10_relat_1(A_143, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_248, c_209])).
% 2.02/1.33  tff(c_269, plain, (k10_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_263])).
% 2.02/1.33  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_269])).
% 2.02/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.33  
% 2.02/1.33  Inference rules
% 2.02/1.33  ----------------------
% 2.02/1.33  #Ref     : 0
% 2.02/1.33  #Sup     : 44
% 2.02/1.33  #Fact    : 0
% 2.02/1.33  #Define  : 0
% 2.02/1.33  #Split   : 2
% 2.02/1.33  #Chain   : 0
% 2.02/1.33  #Close   : 0
% 2.02/1.33  
% 2.02/1.33  Ordering : KBO
% 2.02/1.33  
% 2.02/1.33  Simplification rules
% 2.02/1.33  ----------------------
% 2.02/1.33  #Subsume      : 14
% 2.02/1.33  #Demod        : 14
% 2.02/1.33  #Tautology    : 10
% 2.02/1.33  #SimpNegUnit  : 6
% 2.02/1.33  #BackRed      : 3
% 2.02/1.33  
% 2.02/1.33  #Partial instantiations: 0
% 2.02/1.33  #Strategies tried      : 1
% 2.02/1.33  
% 2.02/1.33  Timing (in seconds)
% 2.02/1.33  ----------------------
% 2.02/1.34  Preprocessing        : 0.29
% 2.02/1.34  Parsing              : 0.15
% 2.02/1.34  CNF conversion       : 0.03
% 2.02/1.34  Main loop            : 0.20
% 2.02/1.34  Inferencing          : 0.08
% 2.02/1.34  Reduction            : 0.05
% 2.02/1.34  Demodulation         : 0.03
% 2.02/1.34  BG Simplification    : 0.01
% 2.02/1.34  Subsumption          : 0.04
% 2.02/1.34  Abstraction          : 0.01
% 2.02/1.34  MUC search           : 0.00
% 2.02/1.34  Cooper               : 0.00
% 2.02/1.34  Total                : 0.52
% 2.02/1.34  Index Insertion      : 0.00
% 2.02/1.34  Index Deletion       : 0.00
% 2.02/1.34  Index Matching       : 0.00
% 2.02/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
