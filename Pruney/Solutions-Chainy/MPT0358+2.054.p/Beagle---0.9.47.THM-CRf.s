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
% DateTime   : Thu Dec  3 09:56:07 EST 2020

% Result     : Theorem 5.29s
% Output     : CNFRefutation 5.29s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 391 expanded)
%              Number of leaves         :   24 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          :  131 ( 954 expanded)
%              Number of equality atoms :   41 ( 280 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_30,plain,(
    ! [A_15] : k1_subset_1(A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_43,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_53,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_42,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_44])).

tff(c_28,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_55,plain,(
    ! [A_14] : r1_tarski('#skF_5',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_28])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_53])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_466,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r2_hidden('#skF_2'(A_84,B_85,C_86),C_86)
      | r2_hidden('#skF_3'(A_84,B_85,C_86),C_86)
      | k4_xboole_0(A_84,B_85) = C_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_479,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k4_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_466])).

tff(c_1143,plain,(
    ! [A_148,B_149,C_150] :
      ( r2_hidden('#skF_2'(A_148,B_149,C_150),A_148)
      | r2_hidden('#skF_3'(A_148,B_149,C_150),B_149)
      | ~ r2_hidden('#skF_3'(A_148,B_149,C_150),A_148)
      | k4_xboole_0(A_148,B_149) = C_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7,C_8),A_6)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1729,plain,(
    ! [A_160,B_161] :
      ( r2_hidden('#skF_3'(A_160,B_161,A_160),B_161)
      | ~ r2_hidden('#skF_3'(A_160,B_161,A_160),A_160)
      | k4_xboole_0(A_160,B_161) = A_160 ) ),
    inference(resolution,[status(thm)],[c_1143,c_14])).

tff(c_1901,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_3'(A_168,B_169,A_168),B_169)
      | k4_xboole_0(A_168,B_169) = A_168 ) ),
    inference(resolution,[status(thm)],[c_479,c_1729])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_101,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_105,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,(
    ! [D_11] :
      ( ~ r2_hidden(D_11,'#skF_5')
      | ~ r2_hidden(D_11,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_10])).

tff(c_3897,plain,(
    ! [A_224] :
      ( ~ r2_hidden('#skF_3'(A_224,k3_subset_1('#skF_4','#skF_5'),A_224),'#skF_5')
      | k4_xboole_0(A_224,k3_subset_1('#skF_4','#skF_5')) = A_224 ) ),
    inference(resolution,[status(thm)],[c_1901,c_109])).

tff(c_3919,plain,(
    k4_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_479,c_3897])).

tff(c_65,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_97,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_148,plain,(
    ! [A_43,B_44,B_45] :
      ( r2_hidden('#skF_1'(A_43,B_44),B_45)
      | ~ r1_tarski(A_43,B_45)
      | r1_tarski(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_372,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_1'(A_70,B_71),'#skF_5')
      | ~ r1_tarski(A_70,k3_subset_1('#skF_4','#skF_5'))
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_148,c_109])).

tff(c_384,plain,(
    ! [B_2] :
      ( ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
      | r1_tarski('#skF_5',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_389,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_384])).

tff(c_335,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | r2_hidden('#skF_3'(A_65,B_66,C_67),C_67)
      | k4_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_348,plain,(
    ! [A_68,C_69] :
      ( r2_hidden('#skF_3'(A_68,A_68,C_69),C_69)
      | k4_xboole_0(A_68,A_68) = C_69 ) ),
    inference(resolution,[status(thm)],[c_24,c_335])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_369,plain,(
    ! [A_68,C_69,B_2] :
      ( r2_hidden('#skF_3'(A_68,A_68,C_69),B_2)
      | ~ r1_tarski(C_69,B_2)
      | k4_xboole_0(A_68,A_68) = C_69 ) ),
    inference(resolution,[status(thm)],[c_348,c_2])).

tff(c_799,plain,(
    ! [A_125,A_126,B_127] :
      ( ~ r2_hidden('#skF_3'(A_125,A_125,k4_xboole_0(A_126,B_127)),B_127)
      | k4_xboole_0(A_126,B_127) = k4_xboole_0(A_125,A_125) ) ),
    inference(resolution,[status(thm)],[c_348,c_10])).

tff(c_819,plain,(
    ! [A_126,B_2,A_68] :
      ( ~ r1_tarski(k4_xboole_0(A_126,B_2),B_2)
      | k4_xboole_0(A_68,A_68) = k4_xboole_0(A_126,B_2) ) ),
    inference(resolution,[status(thm)],[c_369,c_799])).

tff(c_3928,plain,(
    ! [A_68] :
      ( ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
      | k4_xboole_0(A_68,A_68) = k4_xboole_0('#skF_5',k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3919,c_819])).

tff(c_3972,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3919,c_389,c_3928])).

tff(c_482,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_3'(A_87,B_88,A_87),A_87)
      | k4_xboole_0(A_87,B_88) = A_87 ) ),
    inference(resolution,[status(thm)],[c_24,c_466])).

tff(c_503,plain,(
    ! [A_87,B_88,B_2] :
      ( r2_hidden('#skF_3'(A_87,B_88,A_87),B_2)
      | ~ r1_tarski(A_87,B_2)
      | k4_xboole_0(A_87,B_88) = A_87 ) ),
    inference(resolution,[status(thm)],[c_482,c_2])).

tff(c_345,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_335])).

tff(c_4629,plain,(
    ! [A_241,C_242] :
      ( r2_hidden('#skF_3'(A_241,A_241,C_242),C_242)
      | C_242 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_345])).

tff(c_78,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),A_25)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_83,plain,(
    ! [A_6,B_7,B_26] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_26),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_26) ) ),
    inference(resolution,[status(thm)],[c_78,c_12])).

tff(c_91,plain,(
    ! [D_30,B_31,A_32] :
      ( ~ r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k4_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_278,plain,(
    ! [A_55,B_56,B_57] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_55,B_56),B_57),B_56)
      | r1_tarski(k4_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_91])).

tff(c_298,plain,(
    ! [A_6,B_26] : r1_tarski(k4_xboole_0(A_6,A_6),B_26) ),
    inference(resolution,[status(thm)],[c_83,c_278])).

tff(c_837,plain,(
    ! [A_131,B_132,A_133] :
      ( ~ r1_tarski(k4_xboole_0(A_131,B_132),B_132)
      | k4_xboole_0(A_133,A_133) = k4_xboole_0(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_369,c_799])).

tff(c_857,plain,(
    ! [B_134,A_135] : k4_xboole_0(B_134,B_134) = k4_xboole_0(A_135,A_135) ),
    inference(resolution,[status(thm)],[c_298,c_837])).

tff(c_965,plain,(
    ! [D_11,B_134,A_135] :
      ( ~ r2_hidden(D_11,B_134)
      | ~ r2_hidden(D_11,k4_xboole_0(A_135,A_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_10])).

tff(c_3994,plain,(
    ! [D_11,B_134] :
      ( ~ r2_hidden(D_11,B_134)
      | ~ r2_hidden(D_11,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_965])).

tff(c_4718,plain,(
    ! [A_246,C_247] :
      ( ~ r2_hidden('#skF_3'(A_246,A_246,C_247),'#skF_5')
      | C_247 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_4629,c_3994])).

tff(c_4740,plain,(
    ! [B_88] :
      ( B_88 = '#skF_5'
      | ~ r1_tarski(B_88,'#skF_5')
      | k4_xboole_0(B_88,B_88) = B_88 ) ),
    inference(resolution,[status(thm)],[c_503,c_4718])).

tff(c_4757,plain,(
    ! [B_248] :
      ( B_248 = '#skF_5'
      | ~ r1_tarski(B_248,'#skF_5')
      | B_248 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3972,c_4740])).

tff(c_4773,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_4757])).

tff(c_4783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_4773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.29/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.02  
% 5.29/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.02  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.29/2.02  
% 5.29/2.02  %Foreground sorts:
% 5.29/2.02  
% 5.29/2.02  
% 5.29/2.02  %Background operators:
% 5.29/2.02  
% 5.29/2.02  
% 5.29/2.02  %Foreground operators:
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.29/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.29/2.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.29/2.02  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.29/2.02  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.29/2.02  tff('#skF_5', type, '#skF_5': $i).
% 5.29/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.29/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.29/2.02  tff('#skF_4', type, '#skF_4': $i).
% 5.29/2.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.29/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.29/2.02  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.29/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.29/2.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.29/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.29/2.02  
% 5.29/2.04  tff(f_48, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 5.29/2.04  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 5.29/2.04  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.29/2.04  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.29/2.04  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 5.29/2.04  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.29/2.04  tff(c_30, plain, (![A_15]: (k1_subset_1(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.29/2.04  tff(c_36, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.29/2.04  tff(c_43, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 5.29/2.04  tff(c_53, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_43])).
% 5.29/2.04  tff(c_42, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.29/2.04  tff(c_44, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 5.29/2.04  tff(c_54, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_53, c_44])).
% 5.29/2.04  tff(c_28, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.29/2.04  tff(c_55, plain, (![A_14]: (r1_tarski('#skF_5', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_28])).
% 5.29/2.04  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_53])).
% 5.29/2.04  tff(c_64, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_43])).
% 5.29/2.04  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_466, plain, (![A_84, B_85, C_86]: (~r2_hidden('#skF_2'(A_84, B_85, C_86), C_86) | r2_hidden('#skF_3'(A_84, B_85, C_86), C_86) | k4_xboole_0(A_84, B_85)=C_86)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_479, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k4_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_466])).
% 5.29/2.04  tff(c_1143, plain, (![A_148, B_149, C_150]: (r2_hidden('#skF_2'(A_148, B_149, C_150), A_148) | r2_hidden('#skF_3'(A_148, B_149, C_150), B_149) | ~r2_hidden('#skF_3'(A_148, B_149, C_150), A_148) | k4_xboole_0(A_148, B_149)=C_150)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_14, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), B_7) | ~r2_hidden('#skF_3'(A_6, B_7, C_8), A_6) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_1729, plain, (![A_160, B_161]: (r2_hidden('#skF_3'(A_160, B_161, A_160), B_161) | ~r2_hidden('#skF_3'(A_160, B_161, A_160), A_160) | k4_xboole_0(A_160, B_161)=A_160)), inference(resolution, [status(thm)], [c_1143, c_14])).
% 5.29/2.04  tff(c_1901, plain, (![A_168, B_169]: (r2_hidden('#skF_3'(A_168, B_169, A_168), B_169) | k4_xboole_0(A_168, B_169)=A_168)), inference(resolution, [status(thm)], [c_479, c_1729])).
% 5.29/2.04  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.29/2.04  tff(c_101, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.29/2.04  tff(c_105, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_101])).
% 5.29/2.04  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_109, plain, (![D_11]: (~r2_hidden(D_11, '#skF_5') | ~r2_hidden(D_11, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_105, c_10])).
% 5.29/2.04  tff(c_3897, plain, (![A_224]: (~r2_hidden('#skF_3'(A_224, k3_subset_1('#skF_4', '#skF_5'), A_224), '#skF_5') | k4_xboole_0(A_224, k3_subset_1('#skF_4', '#skF_5'))=A_224)), inference(resolution, [status(thm)], [c_1901, c_109])).
% 5.29/2.04  tff(c_3919, plain, (k4_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_479, c_3897])).
% 5.29/2.04  tff(c_65, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_43])).
% 5.29/2.04  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_97, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_148, plain, (![A_43, B_44, B_45]: (r2_hidden('#skF_1'(A_43, B_44), B_45) | ~r1_tarski(A_43, B_45) | r1_tarski(A_43, B_44))), inference(resolution, [status(thm)], [c_6, c_97])).
% 5.29/2.04  tff(c_372, plain, (![A_70, B_71]: (~r2_hidden('#skF_1'(A_70, B_71), '#skF_5') | ~r1_tarski(A_70, k3_subset_1('#skF_4', '#skF_5')) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_148, c_109])).
% 5.29/2.04  tff(c_384, plain, (![B_2]: (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | r1_tarski('#skF_5', B_2))), inference(resolution, [status(thm)], [c_6, c_372])).
% 5.29/2.04  tff(c_389, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_384])).
% 5.29/2.04  tff(c_335, plain, (![A_65, B_66, C_67]: (~r2_hidden('#skF_2'(A_65, B_66, C_67), B_66) | r2_hidden('#skF_3'(A_65, B_66, C_67), C_67) | k4_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_348, plain, (![A_68, C_69]: (r2_hidden('#skF_3'(A_68, A_68, C_69), C_69) | k4_xboole_0(A_68, A_68)=C_69)), inference(resolution, [status(thm)], [c_24, c_335])).
% 5.29/2.04  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_369, plain, (![A_68, C_69, B_2]: (r2_hidden('#skF_3'(A_68, A_68, C_69), B_2) | ~r1_tarski(C_69, B_2) | k4_xboole_0(A_68, A_68)=C_69)), inference(resolution, [status(thm)], [c_348, c_2])).
% 5.29/2.04  tff(c_799, plain, (![A_125, A_126, B_127]: (~r2_hidden('#skF_3'(A_125, A_125, k4_xboole_0(A_126, B_127)), B_127) | k4_xboole_0(A_126, B_127)=k4_xboole_0(A_125, A_125))), inference(resolution, [status(thm)], [c_348, c_10])).
% 5.29/2.04  tff(c_819, plain, (![A_126, B_2, A_68]: (~r1_tarski(k4_xboole_0(A_126, B_2), B_2) | k4_xboole_0(A_68, A_68)=k4_xboole_0(A_126, B_2))), inference(resolution, [status(thm)], [c_369, c_799])).
% 5.29/2.04  tff(c_3928, plain, (![A_68]: (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k4_xboole_0(A_68, A_68)=k4_xboole_0('#skF_5', k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_3919, c_819])).
% 5.29/2.04  tff(c_3972, plain, (![A_68]: (k4_xboole_0(A_68, A_68)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3919, c_389, c_3928])).
% 5.29/2.04  tff(c_482, plain, (![A_87, B_88]: (r2_hidden('#skF_3'(A_87, B_88, A_87), A_87) | k4_xboole_0(A_87, B_88)=A_87)), inference(resolution, [status(thm)], [c_24, c_466])).
% 5.29/2.04  tff(c_503, plain, (![A_87, B_88, B_2]: (r2_hidden('#skF_3'(A_87, B_88, A_87), B_2) | ~r1_tarski(A_87, B_2) | k4_xboole_0(A_87, B_88)=A_87)), inference(resolution, [status(thm)], [c_482, c_2])).
% 5.29/2.04  tff(c_345, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_335])).
% 5.29/2.04  tff(c_4629, plain, (![A_241, C_242]: (r2_hidden('#skF_3'(A_241, A_241, C_242), C_242) | C_242='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_345])).
% 5.29/2.04  tff(c_78, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), A_25) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.29/2.04  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_83, plain, (![A_6, B_7, B_26]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_26), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_26))), inference(resolution, [status(thm)], [c_78, c_12])).
% 5.29/2.04  tff(c_91, plain, (![D_30, B_31, A_32]: (~r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k4_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.29/2.04  tff(c_278, plain, (![A_55, B_56, B_57]: (~r2_hidden('#skF_1'(k4_xboole_0(A_55, B_56), B_57), B_56) | r1_tarski(k4_xboole_0(A_55, B_56), B_57))), inference(resolution, [status(thm)], [c_6, c_91])).
% 5.29/2.04  tff(c_298, plain, (![A_6, B_26]: (r1_tarski(k4_xboole_0(A_6, A_6), B_26))), inference(resolution, [status(thm)], [c_83, c_278])).
% 5.29/2.04  tff(c_837, plain, (![A_131, B_132, A_133]: (~r1_tarski(k4_xboole_0(A_131, B_132), B_132) | k4_xboole_0(A_133, A_133)=k4_xboole_0(A_131, B_132))), inference(resolution, [status(thm)], [c_369, c_799])).
% 5.29/2.04  tff(c_857, plain, (![B_134, A_135]: (k4_xboole_0(B_134, B_134)=k4_xboole_0(A_135, A_135))), inference(resolution, [status(thm)], [c_298, c_837])).
% 5.29/2.04  tff(c_965, plain, (![D_11, B_134, A_135]: (~r2_hidden(D_11, B_134) | ~r2_hidden(D_11, k4_xboole_0(A_135, A_135)))), inference(superposition, [status(thm), theory('equality')], [c_857, c_10])).
% 5.29/2.04  tff(c_3994, plain, (![D_11, B_134]: (~r2_hidden(D_11, B_134) | ~r2_hidden(D_11, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_965])).
% 5.29/2.04  tff(c_4718, plain, (![A_246, C_247]: (~r2_hidden('#skF_3'(A_246, A_246, C_247), '#skF_5') | C_247='#skF_5')), inference(resolution, [status(thm)], [c_4629, c_3994])).
% 5.29/2.04  tff(c_4740, plain, (![B_88]: (B_88='#skF_5' | ~r1_tarski(B_88, '#skF_5') | k4_xboole_0(B_88, B_88)=B_88)), inference(resolution, [status(thm)], [c_503, c_4718])).
% 5.29/2.04  tff(c_4757, plain, (![B_248]: (B_248='#skF_5' | ~r1_tarski(B_248, '#skF_5') | B_248='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3972, c_4740])).
% 5.29/2.04  tff(c_4773, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_28, c_4757])).
% 5.29/2.04  tff(c_4783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_4773])).
% 5.29/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.29/2.04  
% 5.29/2.04  Inference rules
% 5.29/2.04  ----------------------
% 5.29/2.04  #Ref     : 0
% 5.29/2.04  #Sup     : 1295
% 5.29/2.04  #Fact    : 0
% 5.29/2.04  #Define  : 0
% 5.29/2.04  #Split   : 5
% 5.29/2.04  #Chain   : 0
% 5.29/2.04  #Close   : 0
% 5.29/2.04  
% 5.29/2.04  Ordering : KBO
% 5.29/2.04  
% 5.29/2.04  Simplification rules
% 5.29/2.04  ----------------------
% 5.29/2.04  #Subsume      : 409
% 5.29/2.04  #Demod        : 683
% 5.29/2.04  #Tautology    : 392
% 5.29/2.04  #SimpNegUnit  : 3
% 5.29/2.04  #BackRed      : 50
% 5.29/2.04  
% 5.29/2.04  #Partial instantiations: 0
% 5.29/2.04  #Strategies tried      : 1
% 5.29/2.04  
% 5.29/2.04  Timing (in seconds)
% 5.29/2.04  ----------------------
% 5.29/2.04  Preprocessing        : 0.31
% 5.29/2.04  Parsing              : 0.15
% 5.29/2.04  CNF conversion       : 0.02
% 5.29/2.04  Main loop            : 0.97
% 5.29/2.04  Inferencing          : 0.30
% 5.29/2.04  Reduction            : 0.33
% 5.29/2.04  Demodulation         : 0.25
% 5.29/2.04  BG Simplification    : 0.04
% 5.29/2.04  Subsumption          : 0.23
% 5.29/2.04  Abstraction          : 0.06
% 5.29/2.04  MUC search           : 0.00
% 5.29/2.04  Cooper               : 0.00
% 5.29/2.04  Total                : 1.31
% 5.29/2.04  Index Insertion      : 0.00
% 5.29/2.04  Index Deletion       : 0.00
% 5.29/2.04  Index Matching       : 0.00
% 5.29/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
