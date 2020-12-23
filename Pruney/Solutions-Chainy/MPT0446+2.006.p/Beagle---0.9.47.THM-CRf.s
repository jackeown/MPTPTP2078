%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 101 expanded)
%              Number of leaves         :   39 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 138 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_85,plain,(
    ~ r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_66,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    ! [A_57] :
      ( k2_xboole_0(k1_relat_1(A_57),k2_relat_1(A_57)) = k3_relat_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_87,plain,(
    ! [A_71,B_72] : k3_tarski(k2_tarski(A_71,B_72)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(A_14,k1_zfmisc_1(k3_tarski(A_14))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_71,B_72] : r1_tarski(k2_tarski(A_71,B_72),k1_zfmisc_1(k2_xboole_0(A_71,B_72))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_28])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_253,plain,(
    ! [C_118,B_119,A_120] :
      ( r2_hidden(C_118,B_119)
      | ~ r2_hidden(C_118,A_120)
      | ~ r1_tarski(A_120,B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_388,plain,(
    ! [D_131,B_132,B_133] :
      ( r2_hidden(D_131,B_132)
      | ~ r1_tarski(k2_tarski(D_131,B_133),B_132) ) ),
    inference(resolution,[status(thm)],[c_12,c_253])).

tff(c_405,plain,(
    ! [A_134,B_135] : r2_hidden(A_134,k1_zfmisc_1(k2_xboole_0(A_134,B_135))) ),
    inference(resolution,[status(thm)],[c_93,c_388])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_427,plain,(
    ! [A_136,B_137] : m1_subset_1(A_136,k1_zfmisc_1(k2_xboole_0(A_136,B_137))) ),
    inference(resolution,[status(thm)],[c_405,c_30])).

tff(c_32,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_456,plain,(
    ! [A_140,B_141] : r1_tarski(A_140,k2_xboole_0(A_140,B_141)) ),
    inference(resolution,[status(thm)],[c_427,c_32])).

tff(c_64,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_163,plain,(
    ! [C_96,A_97,D_98] :
      ( r2_hidden(C_96,k1_relat_1(A_97))
      | ~ r2_hidden(k4_tarski(C_96,D_98),A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_187,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_64,c_163])).

tff(c_276,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_12',B_119)
      | ~ r1_tarski(k1_relat_1('#skF_14'),B_119) ) ),
    inference(resolution,[status(thm)],[c_187,c_253])).

tff(c_483,plain,(
    ! [B_143] : r2_hidden('#skF_12',k2_xboole_0(k1_relat_1('#skF_14'),B_143)) ),
    inference(resolution,[status(thm)],[c_456,c_276])).

tff(c_492,plain,
    ( r2_hidden('#skF_12',k3_relat_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_483])).

tff(c_496,plain,(
    r2_hidden('#skF_12',k3_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_492])).

tff(c_498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_496])).

tff(c_499,plain,(
    ~ r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_511,plain,(
    ! [A_148,B_149] : k3_tarski(k2_tarski(A_148,B_149)) = k2_xboole_0(A_148,B_149) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_517,plain,(
    ! [A_148,B_149] : r1_tarski(k2_tarski(A_148,B_149),k1_zfmisc_1(k2_xboole_0(A_148,B_149))) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_28])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_589,plain,(
    ! [C_166,B_167,A_168] :
      ( r2_hidden(C_166,B_167)
      | ~ r2_hidden(C_166,A_168)
      | ~ r1_tarski(A_168,B_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_989,plain,(
    ! [D_217,B_218,A_219] :
      ( r2_hidden(D_217,B_218)
      | ~ r1_tarski(k2_tarski(A_219,D_217),B_218) ) ),
    inference(resolution,[status(thm)],[c_10,c_589])).

tff(c_1011,plain,(
    ! [B_220,A_221] : r2_hidden(B_220,k1_zfmisc_1(k2_xboole_0(A_221,B_220))) ),
    inference(resolution,[status(thm)],[c_517,c_989])).

tff(c_1034,plain,(
    ! [B_224,A_225] : m1_subset_1(B_224,k1_zfmisc_1(k2_xboole_0(A_225,B_224))) ),
    inference(resolution,[status(thm)],[c_1011,c_30])).

tff(c_1042,plain,(
    ! [B_226,A_227] : r1_tarski(B_226,k2_xboole_0(A_227,B_226)) ),
    inference(resolution,[status(thm)],[c_1034,c_32])).

tff(c_570,plain,(
    ! [C_163,A_164,D_165] :
      ( r2_hidden(C_163,k2_relat_1(A_164))
      | ~ r2_hidden(k4_tarski(D_165,C_163),A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_584,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_64,c_570])).

tff(c_602,plain,(
    ! [B_167] :
      ( r2_hidden('#skF_13',B_167)
      | ~ r1_tarski(k2_relat_1('#skF_14'),B_167) ) ),
    inference(resolution,[status(thm)],[c_584,c_589])).

tff(c_1082,plain,(
    ! [A_229] : r2_hidden('#skF_13',k2_xboole_0(A_229,k2_relat_1('#skF_14'))) ),
    inference(resolution,[status(thm)],[c_1042,c_602])).

tff(c_1091,plain,
    ( r2_hidden('#skF_13',k3_relat_1('#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1082])).

tff(c_1095,plain,(
    r2_hidden('#skF_13',k3_relat_1('#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1091])).

tff(c_1097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_1095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:34 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.05/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.05/1.52  
% 3.05/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_6 > #skF_14 > #skF_13 > #skF_10 > #skF_2 > #skF_8 > #skF_11 > #skF_7 > #skF_3 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 3.32/1.52  
% 3.32/1.52  %Foreground sorts:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Background operators:
% 3.32/1.52  
% 3.32/1.52  
% 3.32/1.52  %Foreground operators:
% 3.32/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.32/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.32/1.52  tff('#skF_14', type, '#skF_14': $i).
% 3.32/1.52  tff('#skF_13', type, '#skF_13': $i).
% 3.32/1.52  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.32/1.52  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 3.32/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.52  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.32/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.32/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.32/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.32/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.52  tff('#skF_12', type, '#skF_12': $i).
% 3.32/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.32/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.52  
% 3.32/1.54  tff(f_82, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 3.32/1.54  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.32/1.54  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.32/1.54  tff(f_45, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.32/1.54  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.32/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.32/1.54  tff(f_49, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.32/1.54  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.32/1.54  tff(f_61, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.32/1.54  tff(f_69, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.32/1.54  tff(c_62, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_14')) | ~r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.54  tff(c_85, plain, (~r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.32/1.54  tff(c_66, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.54  tff(c_60, plain, (![A_57]: (k2_xboole_0(k1_relat_1(A_57), k2_relat_1(A_57))=k3_relat_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/1.54  tff(c_87, plain, (![A_71, B_72]: (k3_tarski(k2_tarski(A_71, B_72))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.54  tff(c_28, plain, (![A_14]: (r1_tarski(A_14, k1_zfmisc_1(k3_tarski(A_14))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.54  tff(c_93, plain, (![A_71, B_72]: (r1_tarski(k2_tarski(A_71, B_72), k1_zfmisc_1(k2_xboole_0(A_71, B_72))))), inference(superposition, [status(thm), theory('equality')], [c_87, c_28])).
% 3.32/1.54  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.54  tff(c_253, plain, (![C_118, B_119, A_120]: (r2_hidden(C_118, B_119) | ~r2_hidden(C_118, A_120) | ~r1_tarski(A_120, B_119))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.54  tff(c_388, plain, (![D_131, B_132, B_133]: (r2_hidden(D_131, B_132) | ~r1_tarski(k2_tarski(D_131, B_133), B_132))), inference(resolution, [status(thm)], [c_12, c_253])).
% 3.32/1.54  tff(c_405, plain, (![A_134, B_135]: (r2_hidden(A_134, k1_zfmisc_1(k2_xboole_0(A_134, B_135))))), inference(resolution, [status(thm)], [c_93, c_388])).
% 3.32/1.54  tff(c_30, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.54  tff(c_427, plain, (![A_136, B_137]: (m1_subset_1(A_136, k1_zfmisc_1(k2_xboole_0(A_136, B_137))))), inference(resolution, [status(thm)], [c_405, c_30])).
% 3.32/1.54  tff(c_32, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.54  tff(c_456, plain, (![A_140, B_141]: (r1_tarski(A_140, k2_xboole_0(A_140, B_141)))), inference(resolution, [status(thm)], [c_427, c_32])).
% 3.32/1.54  tff(c_64, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.32/1.54  tff(c_163, plain, (![C_96, A_97, D_98]: (r2_hidden(C_96, k1_relat_1(A_97)) | ~r2_hidden(k4_tarski(C_96, D_98), A_97))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.54  tff(c_187, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_64, c_163])).
% 3.32/1.54  tff(c_276, plain, (![B_119]: (r2_hidden('#skF_12', B_119) | ~r1_tarski(k1_relat_1('#skF_14'), B_119))), inference(resolution, [status(thm)], [c_187, c_253])).
% 3.32/1.54  tff(c_483, plain, (![B_143]: (r2_hidden('#skF_12', k2_xboole_0(k1_relat_1('#skF_14'), B_143)))), inference(resolution, [status(thm)], [c_456, c_276])).
% 3.32/1.54  tff(c_492, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_60, c_483])).
% 3.32/1.54  tff(c_496, plain, (r2_hidden('#skF_12', k3_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_492])).
% 3.32/1.54  tff(c_498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_496])).
% 3.32/1.54  tff(c_499, plain, (~r2_hidden('#skF_13', k3_relat_1('#skF_14'))), inference(splitRight, [status(thm)], [c_62])).
% 3.32/1.54  tff(c_511, plain, (![A_148, B_149]: (k3_tarski(k2_tarski(A_148, B_149))=k2_xboole_0(A_148, B_149))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.54  tff(c_517, plain, (![A_148, B_149]: (r1_tarski(k2_tarski(A_148, B_149), k1_zfmisc_1(k2_xboole_0(A_148, B_149))))), inference(superposition, [status(thm), theory('equality')], [c_511, c_28])).
% 3.32/1.54  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.32/1.54  tff(c_589, plain, (![C_166, B_167, A_168]: (r2_hidden(C_166, B_167) | ~r2_hidden(C_166, A_168) | ~r1_tarski(A_168, B_167))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.32/1.54  tff(c_989, plain, (![D_217, B_218, A_219]: (r2_hidden(D_217, B_218) | ~r1_tarski(k2_tarski(A_219, D_217), B_218))), inference(resolution, [status(thm)], [c_10, c_589])).
% 3.32/1.54  tff(c_1011, plain, (![B_220, A_221]: (r2_hidden(B_220, k1_zfmisc_1(k2_xboole_0(A_221, B_220))))), inference(resolution, [status(thm)], [c_517, c_989])).
% 3.32/1.54  tff(c_1034, plain, (![B_224, A_225]: (m1_subset_1(B_224, k1_zfmisc_1(k2_xboole_0(A_225, B_224))))), inference(resolution, [status(thm)], [c_1011, c_30])).
% 3.32/1.54  tff(c_1042, plain, (![B_226, A_227]: (r1_tarski(B_226, k2_xboole_0(A_227, B_226)))), inference(resolution, [status(thm)], [c_1034, c_32])).
% 3.32/1.54  tff(c_570, plain, (![C_163, A_164, D_165]: (r2_hidden(C_163, k2_relat_1(A_164)) | ~r2_hidden(k4_tarski(D_165, C_163), A_164))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.32/1.54  tff(c_584, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_64, c_570])).
% 3.32/1.54  tff(c_602, plain, (![B_167]: (r2_hidden('#skF_13', B_167) | ~r1_tarski(k2_relat_1('#skF_14'), B_167))), inference(resolution, [status(thm)], [c_584, c_589])).
% 3.32/1.54  tff(c_1082, plain, (![A_229]: (r2_hidden('#skF_13', k2_xboole_0(A_229, k2_relat_1('#skF_14'))))), inference(resolution, [status(thm)], [c_1042, c_602])).
% 3.32/1.54  tff(c_1091, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_14')) | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_60, c_1082])).
% 3.32/1.54  tff(c_1095, plain, (r2_hidden('#skF_13', k3_relat_1('#skF_14'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1091])).
% 3.32/1.54  tff(c_1097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_1095])).
% 3.32/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.54  
% 3.32/1.54  Inference rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Ref     : 0
% 3.32/1.54  #Sup     : 225
% 3.32/1.54  #Fact    : 0
% 3.32/1.54  #Define  : 0
% 3.32/1.54  #Split   : 1
% 3.32/1.54  #Chain   : 0
% 3.32/1.54  #Close   : 0
% 3.32/1.54  
% 3.32/1.54  Ordering : KBO
% 3.32/1.54  
% 3.32/1.54  Simplification rules
% 3.32/1.54  ----------------------
% 3.32/1.54  #Subsume      : 1
% 3.32/1.54  #Demod        : 22
% 3.32/1.54  #Tautology    : 30
% 3.32/1.54  #SimpNegUnit  : 2
% 3.32/1.54  #BackRed      : 0
% 3.32/1.54  
% 3.32/1.54  #Partial instantiations: 0
% 3.32/1.54  #Strategies tried      : 1
% 3.32/1.54  
% 3.32/1.54  Timing (in seconds)
% 3.32/1.54  ----------------------
% 3.32/1.54  Preprocessing        : 0.31
% 3.32/1.54  Parsing              : 0.17
% 3.32/1.54  CNF conversion       : 0.03
% 3.32/1.54  Main loop            : 0.43
% 3.32/1.54  Inferencing          : 0.16
% 3.32/1.54  Reduction            : 0.13
% 3.32/1.54  Demodulation         : 0.09
% 3.32/1.54  BG Simplification    : 0.02
% 3.32/1.54  Subsumption          : 0.08
% 3.32/1.54  Abstraction          : 0.02
% 3.32/1.54  MUC search           : 0.00
% 3.32/1.54  Cooper               : 0.00
% 3.32/1.54  Total                : 0.77
% 3.32/1.54  Index Insertion      : 0.00
% 3.32/1.54  Index Deletion       : 0.00
% 3.32/1.54  Index Matching       : 0.00
% 3.32/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
