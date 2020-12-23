%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 251 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  155 ( 492 expanded)
%              Number of equality atoms :   28 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_142,plain,(
    ! [A_46,B_47] :
      ( r2_hidden('#skF_2'(A_46,B_47),A_46)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_142,c_4])).

tff(c_34,plain,(
    ! [A_22] : k1_subset_1(A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,
    ( k1_subset_1('#skF_4') != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_49,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_111,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_49])).

tff(c_199,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_111])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( ~ r2_hidden('#skF_2'(A_7,B_8),B_8)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_150,plain,(
    ! [A_46] : r1_tarski(A_46,A_46) ),
    inference(resolution,[status(thm)],[c_142,c_10])).

tff(c_202,plain,(
    ! [C_57,B_58,A_59] :
      ( r2_hidden(C_57,B_58)
      | ~ r2_hidden(C_57,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_211,plain,(
    ! [A_3,B_58] :
      ( r2_hidden('#skF_1'(A_3),B_58)
      | ~ r1_tarski(A_3,B_58)
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_48,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_subset_1('#skF_4') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_50,plain,
    ( r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5'))
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_48])).

tff(c_112,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_50])).

tff(c_32,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_115,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_32])).

tff(c_303,plain,(
    ! [A_75,C_76,B_77] :
      ( ~ r2_hidden(A_75,C_76)
      | ~ r2_hidden(A_75,B_77)
      | ~ r2_hidden(A_75,k5_xboole_0(B_77,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_338,plain,(
    ! [A_78,A_79] :
      ( ~ r2_hidden(A_78,A_79)
      | ~ r2_hidden(A_78,A_79)
      | ~ r2_hidden(A_78,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_303])).

tff(c_404,plain,(
    ! [A_88] :
      ( ~ r2_hidden('#skF_1'(A_88),A_88)
      | ~ r2_hidden('#skF_1'(A_88),'#skF_5')
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_6,c_338])).

tff(c_410,plain,(
    ! [B_58] :
      ( ~ r2_hidden('#skF_1'(B_58),'#skF_5')
      | ~ r1_tarski(B_58,B_58)
      | v1_xboole_0(B_58) ) ),
    inference(resolution,[status(thm)],[c_211,c_404])).

tff(c_418,plain,(
    ! [B_89] :
      ( ~ r2_hidden('#skF_1'(B_89),'#skF_5')
      | v1_xboole_0(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_410])).

tff(c_430,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_418])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_199,c_199,c_430])).

tff(c_437,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_2'(A_7,B_8),A_7)
      | r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_483,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden('#skF_2'(A_98,B_99),B_99)
      | r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_488,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(resolution,[status(thm)],[c_12,c_483])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_585,plain,(
    ! [C_112,A_113,B_114] :
      ( r2_hidden(C_112,A_113)
      | ~ r2_hidden(C_112,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1497,plain,(
    ! [A_181,B_182,A_183] :
      ( r2_hidden('#skF_2'(A_181,B_182),A_183)
      | ~ m1_subset_1(A_181,k1_zfmisc_1(A_183))
      | r1_tarski(A_181,B_182) ) ),
    inference(resolution,[status(thm)],[c_12,c_585])).

tff(c_1535,plain,(
    ! [A_184,A_185] :
      ( ~ m1_subset_1(A_184,k1_zfmisc_1(A_185))
      | r1_tarski(A_184,A_185) ) ),
    inference(resolution,[status(thm)],[c_1497,c_10])).

tff(c_1539,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1535])).

tff(c_494,plain,(
    ! [C_101,B_102,A_103] :
      ( r2_hidden(C_101,B_102)
      | ~ r2_hidden(C_101,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_563,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_1'(A_108),B_109)
      | ~ r1_tarski(A_108,B_109)
      | v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_6,c_494])).

tff(c_8,plain,(
    ! [C_11,B_8,A_7] :
      ( r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2498,plain,(
    ! [A_229,B_230,B_231] :
      ( r2_hidden('#skF_1'(A_229),B_230)
      | ~ r1_tarski(B_231,B_230)
      | ~ r1_tarski(A_229,B_231)
      | v1_xboole_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_563,c_8])).

tff(c_2608,plain,(
    ! [A_235] :
      ( r2_hidden('#skF_1'(A_235),'#skF_4')
      | ~ r1_tarski(A_235,'#skF_5')
      | v1_xboole_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_1539,c_2498])).

tff(c_2620,plain,(
    ! [A_235,B_8] :
      ( r2_hidden('#skF_1'(A_235),B_8)
      | ~ r1_tarski('#skF_4',B_8)
      | ~ r1_tarski(A_235,'#skF_5')
      | v1_xboole_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_2608,c_8])).

tff(c_438,plain,(
    r1_tarski('#skF_5',k3_subset_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_49])).

tff(c_2622,plain,(
    ! [A_236] :
      ( r2_hidden('#skF_1'(A_236),k3_subset_1('#skF_4','#skF_5'))
      | ~ r1_tarski(A_236,'#skF_5')
      | v1_xboole_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_438,c_2498])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1555,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1539,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1565,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_2])).

tff(c_623,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(A_119,B_120) = k3_subset_1(A_119,B_120)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_627,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_623])).

tff(c_28,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k3_xboole_0(A_17,B_18)) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1194,plain,(
    ! [A_159,C_160,B_161] :
      ( ~ r2_hidden(A_159,C_160)
      | ~ r2_hidden(A_159,B_161)
      | ~ r2_hidden(A_159,k5_xboole_0(B_161,C_160)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1749,plain,(
    ! [A_200,A_201,B_202] :
      ( ~ r2_hidden(A_200,k3_xboole_0(A_201,B_202))
      | ~ r2_hidden(A_200,A_201)
      | ~ r2_hidden(A_200,k4_xboole_0(A_201,B_202)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1194])).

tff(c_1787,plain,(
    ! [A_200] :
      ( ~ r2_hidden(A_200,k3_xboole_0('#skF_4','#skF_5'))
      | ~ r2_hidden(A_200,'#skF_4')
      | ~ r2_hidden(A_200,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_1749])).

tff(c_1826,plain,(
    ! [A_200] :
      ( ~ r2_hidden(A_200,'#skF_5')
      | ~ r2_hidden(A_200,'#skF_4')
      | ~ r2_hidden(A_200,k3_subset_1('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_1787])).

tff(c_7505,plain,(
    ! [A_372] :
      ( ~ r2_hidden('#skF_1'(A_372),'#skF_5')
      | ~ r2_hidden('#skF_1'(A_372),'#skF_4')
      | ~ r1_tarski(A_372,'#skF_5')
      | v1_xboole_0(A_372) ) ),
    inference(resolution,[status(thm)],[c_2622,c_1826])).

tff(c_7541,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_7505])).

tff(c_7552,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_7541])).

tff(c_7553,plain,(
    ~ r2_hidden('#skF_1'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7552])).

tff(c_7559,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2620,c_7553])).

tff(c_7574,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_7559])).

tff(c_71,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_3'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_7596,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7574,c_75])).

tff(c_7604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_7596])).

tff(c_7605,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_7552])).

tff(c_7619,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7605,c_75])).

tff(c_7627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_7619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.30  
% 6.45/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.30  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 6.45/2.30  
% 6.45/2.30  %Foreground sorts:
% 6.45/2.30  
% 6.45/2.30  
% 6.45/2.30  %Background operators:
% 6.45/2.30  
% 6.45/2.30  
% 6.45/2.30  %Foreground operators:
% 6.45/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.45/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.45/2.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.45/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.45/2.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.45/2.30  tff('#skF_5', type, '#skF_5': $i).
% 6.45/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.30  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.45/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.45/2.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 6.45/2.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.45/2.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.45/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.30  
% 6.45/2.32  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.45/2.32  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.45/2.32  tff(f_65, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 6.45/2.32  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 6.45/2.32  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.45/2.32  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.45/2.32  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 6.45/2.32  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.45/2.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.45/2.32  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.45/2.32  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.45/2.32  tff(f_55, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.45/2.32  tff(c_142, plain, (![A_46, B_47]: (r2_hidden('#skF_2'(A_46, B_47), A_46) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.45/2.32  tff(c_192, plain, (![A_53, B_54]: (~v1_xboole_0(A_53) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_142, c_4])).
% 6.45/2.32  tff(c_34, plain, (![A_22]: (k1_subset_1(A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.45/2.32  tff(c_42, plain, (k1_subset_1('#skF_4')!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.45/2.32  tff(c_49, plain, (k1_xboole_0!='#skF_5' | ~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 6.45/2.32  tff(c_111, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_49])).
% 6.45/2.32  tff(c_199, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_192, c_111])).
% 6.45/2.32  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.45/2.32  tff(c_10, plain, (![A_7, B_8]: (~r2_hidden('#skF_2'(A_7, B_8), B_8) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_150, plain, (![A_46]: (r1_tarski(A_46, A_46))), inference(resolution, [status(thm)], [c_142, c_10])).
% 6.45/2.32  tff(c_202, plain, (![C_57, B_58, A_59]: (r2_hidden(C_57, B_58) | ~r2_hidden(C_57, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_211, plain, (![A_3, B_58]: (r2_hidden('#skF_1'(A_3), B_58) | ~r1_tarski(A_3, B_58) | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_202])).
% 6.45/2.32  tff(c_48, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_subset_1('#skF_4')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.45/2.32  tff(c_50, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5')) | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_48])).
% 6.45/2.32  tff(c_112, plain, (k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_111, c_50])).
% 6.45/2.32  tff(c_32, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.45/2.32  tff(c_115, plain, (![A_21]: (k5_xboole_0(A_21, A_21)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_32])).
% 6.45/2.32  tff(c_303, plain, (![A_75, C_76, B_77]: (~r2_hidden(A_75, C_76) | ~r2_hidden(A_75, B_77) | ~r2_hidden(A_75, k5_xboole_0(B_77, C_76)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.45/2.32  tff(c_338, plain, (![A_78, A_79]: (~r2_hidden(A_78, A_79) | ~r2_hidden(A_78, A_79) | ~r2_hidden(A_78, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_303])).
% 6.45/2.32  tff(c_404, plain, (![A_88]: (~r2_hidden('#skF_1'(A_88), A_88) | ~r2_hidden('#skF_1'(A_88), '#skF_5') | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_6, c_338])).
% 6.45/2.32  tff(c_410, plain, (![B_58]: (~r2_hidden('#skF_1'(B_58), '#skF_5') | ~r1_tarski(B_58, B_58) | v1_xboole_0(B_58))), inference(resolution, [status(thm)], [c_211, c_404])).
% 6.45/2.32  tff(c_418, plain, (![B_89]: (~r2_hidden('#skF_1'(B_89), '#skF_5') | v1_xboole_0(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_410])).
% 6.45/2.32  tff(c_430, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_418])).
% 6.45/2.32  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_199, c_199, c_430])).
% 6.45/2.32  tff(c_437, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_49])).
% 6.45/2.32  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_2'(A_7, B_8), A_7) | r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_483, plain, (![A_98, B_99]: (~r2_hidden('#skF_2'(A_98, B_99), B_99) | r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_488, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(resolution, [status(thm)], [c_12, c_483])).
% 6.45/2.32  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.45/2.32  tff(c_585, plain, (![C_112, A_113, B_114]: (r2_hidden(C_112, A_113) | ~r2_hidden(C_112, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.45/2.32  tff(c_1497, plain, (![A_181, B_182, A_183]: (r2_hidden('#skF_2'(A_181, B_182), A_183) | ~m1_subset_1(A_181, k1_zfmisc_1(A_183)) | r1_tarski(A_181, B_182))), inference(resolution, [status(thm)], [c_12, c_585])).
% 6.45/2.32  tff(c_1535, plain, (![A_184, A_185]: (~m1_subset_1(A_184, k1_zfmisc_1(A_185)) | r1_tarski(A_184, A_185))), inference(resolution, [status(thm)], [c_1497, c_10])).
% 6.45/2.32  tff(c_1539, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_1535])).
% 6.45/2.32  tff(c_494, plain, (![C_101, B_102, A_103]: (r2_hidden(C_101, B_102) | ~r2_hidden(C_101, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_563, plain, (![A_108, B_109]: (r2_hidden('#skF_1'(A_108), B_109) | ~r1_tarski(A_108, B_109) | v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_6, c_494])).
% 6.45/2.32  tff(c_8, plain, (![C_11, B_8, A_7]: (r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.45/2.32  tff(c_2498, plain, (![A_229, B_230, B_231]: (r2_hidden('#skF_1'(A_229), B_230) | ~r1_tarski(B_231, B_230) | ~r1_tarski(A_229, B_231) | v1_xboole_0(A_229))), inference(resolution, [status(thm)], [c_563, c_8])).
% 6.45/2.32  tff(c_2608, plain, (![A_235]: (r2_hidden('#skF_1'(A_235), '#skF_4') | ~r1_tarski(A_235, '#skF_5') | v1_xboole_0(A_235))), inference(resolution, [status(thm)], [c_1539, c_2498])).
% 6.45/2.32  tff(c_2620, plain, (![A_235, B_8]: (r2_hidden('#skF_1'(A_235), B_8) | ~r1_tarski('#skF_4', B_8) | ~r1_tarski(A_235, '#skF_5') | v1_xboole_0(A_235))), inference(resolution, [status(thm)], [c_2608, c_8])).
% 6.45/2.32  tff(c_438, plain, (r1_tarski('#skF_5', k3_subset_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_49])).
% 6.45/2.32  tff(c_2622, plain, (![A_236]: (r2_hidden('#skF_1'(A_236), k3_subset_1('#skF_4', '#skF_5')) | ~r1_tarski(A_236, '#skF_5') | v1_xboole_0(A_236))), inference(resolution, [status(thm)], [c_438, c_2498])).
% 6.45/2.32  tff(c_30, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.45/2.32  tff(c_1555, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1539, c_30])).
% 6.45/2.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.45/2.32  tff(c_1565, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_1555, c_2])).
% 6.45/2.32  tff(c_623, plain, (![A_119, B_120]: (k4_xboole_0(A_119, B_120)=k3_subset_1(A_119, B_120) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.45/2.32  tff(c_627, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_623])).
% 6.45/2.32  tff(c_28, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k3_xboole_0(A_17, B_18))=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.45/2.32  tff(c_1194, plain, (![A_159, C_160, B_161]: (~r2_hidden(A_159, C_160) | ~r2_hidden(A_159, B_161) | ~r2_hidden(A_159, k5_xboole_0(B_161, C_160)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.45/2.32  tff(c_1749, plain, (![A_200, A_201, B_202]: (~r2_hidden(A_200, k3_xboole_0(A_201, B_202)) | ~r2_hidden(A_200, A_201) | ~r2_hidden(A_200, k4_xboole_0(A_201, B_202)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1194])).
% 6.45/2.32  tff(c_1787, plain, (![A_200]: (~r2_hidden(A_200, k3_xboole_0('#skF_4', '#skF_5')) | ~r2_hidden(A_200, '#skF_4') | ~r2_hidden(A_200, k3_subset_1('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_627, c_1749])).
% 6.45/2.32  tff(c_1826, plain, (![A_200]: (~r2_hidden(A_200, '#skF_5') | ~r2_hidden(A_200, '#skF_4') | ~r2_hidden(A_200, k3_subset_1('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_1787])).
% 6.45/2.32  tff(c_7505, plain, (![A_372]: (~r2_hidden('#skF_1'(A_372), '#skF_5') | ~r2_hidden('#skF_1'(A_372), '#skF_4') | ~r1_tarski(A_372, '#skF_5') | v1_xboole_0(A_372))), inference(resolution, [status(thm)], [c_2622, c_1826])).
% 6.45/2.32  tff(c_7541, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_4') | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_6, c_7505])).
% 6.45/2.32  tff(c_7552, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_7541])).
% 6.45/2.32  tff(c_7553, plain, (~r2_hidden('#skF_1'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7552])).
% 6.45/2.32  tff(c_7559, plain, (~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_5', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_2620, c_7553])).
% 6.45/2.32  tff(c_7574, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_7559])).
% 6.45/2.32  tff(c_71, plain, (![A_34]: (r2_hidden('#skF_3'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.32  tff(c_75, plain, (![A_34]: (~v1_xboole_0(A_34) | k1_xboole_0=A_34)), inference(resolution, [status(thm)], [c_71, c_4])).
% 6.45/2.32  tff(c_7596, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7574, c_75])).
% 6.45/2.32  tff(c_7604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_7596])).
% 6.45/2.32  tff(c_7605, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_7552])).
% 6.45/2.32  tff(c_7619, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7605, c_75])).
% 6.45/2.32  tff(c_7627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_7619])).
% 6.45/2.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.45/2.32  
% 6.45/2.32  Inference rules
% 6.45/2.32  ----------------------
% 6.45/2.32  #Ref     : 0
% 6.45/2.32  #Sup     : 1723
% 6.45/2.32  #Fact    : 4
% 6.45/2.32  #Define  : 0
% 6.45/2.32  #Split   : 16
% 6.45/2.32  #Chain   : 0
% 6.45/2.32  #Close   : 0
% 6.45/2.32  
% 6.45/2.32  Ordering : KBO
% 6.45/2.32  
% 6.45/2.32  Simplification rules
% 6.45/2.32  ----------------------
% 6.45/2.32  #Subsume      : 594
% 6.45/2.32  #Demod        : 850
% 6.45/2.32  #Tautology    : 441
% 6.45/2.32  #SimpNegUnit  : 115
% 6.45/2.32  #BackRed      : 22
% 6.45/2.32  
% 6.45/2.32  #Partial instantiations: 0
% 6.45/2.32  #Strategies tried      : 1
% 6.45/2.32  
% 6.45/2.32  Timing (in seconds)
% 6.45/2.32  ----------------------
% 6.45/2.32  Preprocessing        : 0.29
% 6.45/2.32  Parsing              : 0.15
% 6.45/2.32  CNF conversion       : 0.02
% 6.45/2.32  Main loop            : 1.22
% 6.45/2.32  Inferencing          : 0.38
% 6.45/2.32  Reduction            : 0.39
% 6.45/2.32  Demodulation         : 0.27
% 6.45/2.32  BG Simplification    : 0.04
% 6.45/2.32  Subsumption          : 0.32
% 6.45/2.32  Abstraction          : 0.05
% 6.45/2.32  MUC search           : 0.00
% 6.45/2.32  Cooper               : 0.00
% 6.45/2.32  Total                : 1.54
% 6.45/2.32  Index Insertion      : 0.00
% 6.45/2.32  Index Deletion       : 0.00
% 6.45/2.32  Index Matching       : 0.00
% 6.45/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
