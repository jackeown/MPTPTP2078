%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 135 expanded)
%              Number of leaves         :   33 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 229 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_79,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1034,plain,(
    ! [B_115,A_116] :
      ( r2_hidden(B_115,A_116)
      | ~ m1_subset_1(B_115,A_116)
      | v1_xboole_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_19] : k3_tarski(k1_zfmisc_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_107,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,k3_tarski(B_39))
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_110,plain,(
    ! [A_38,A_19] :
      ( r1_tarski(A_38,A_19)
      | ~ r2_hidden(A_38,k1_zfmisc_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_107])).

tff(c_1038,plain,(
    ! [B_115,A_19] :
      ( r1_tarski(B_115,A_19)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1034,c_110])).

tff(c_1042,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(B_117,A_118)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_118)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1038])).

tff(c_1054,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1042])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_111,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_311,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_323,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_311])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_149,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | ~ m1_subset_1(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_156,plain,(
    ! [B_52,A_19] :
      ( r1_tarski(B_52,A_19)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_149,c_110])).

tff(c_176,plain,(
    ! [B_54,A_55] :
      ( r1_tarski(B_54,A_55)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_156])).

tff(c_188,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_193,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_188,c_8])).

tff(c_214,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_193])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_279,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_6])).

tff(c_369,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_279])).

tff(c_112,plain,(
    ! [A_40,B_41] : r1_xboole_0(k3_xboole_0(A_40,B_41),k5_xboole_0(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_1,B_2] : r1_xboole_0(k3_xboole_0(A_1,B_2),k5_xboole_0(B_2,A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_201,plain,(
    r1_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_118])).

tff(c_370,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_201])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_161,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_46])).

tff(c_441,plain,(
    ! [C_70,A_71,B_72] :
      ( r1_tarski(C_70,k3_subset_1(A_71,B_72))
      | ~ r1_tarski(B_72,k3_subset_1(A_71,C_70))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_445,plain,
    ( r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_161,c_441])).

tff(c_451,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_445])).

tff(c_460,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_451,c_8])).

tff(c_464,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_6])).

tff(c_473,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_464])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( ~ r1_xboole_0(A_10,k4_xboole_0(B_11,C_12))
      | ~ r1_xboole_0(A_10,C_12)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_481,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r1_xboole_0(A_10,k3_subset_1('#skF_1','#skF_2'))
      | r1_xboole_0(A_10,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_12])).

tff(c_964,plain,(
    ! [A_102] :
      ( ~ r1_xboole_0(A_102,k3_subset_1('#skF_1','#skF_2'))
      | r1_xboole_0(A_102,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_481])).

tff(c_967,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_370,c_964])).

tff(c_971,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_967])).

tff(c_973,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1156,plain,(
    ! [A_121,B_122] :
      ( k4_xboole_0(A_121,B_122) = k3_subset_1(A_121,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1169,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1156])).

tff(c_1219,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(A_126,k4_xboole_0(B_127,C_128))
      | ~ r1_xboole_0(A_126,C_128)
      | ~ r1_tarski(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1498,plain,(
    ! [A_148] :
      ( r1_tarski(A_148,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_148,'#skF_3')
      | ~ r1_tarski(A_148,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_1219])).

tff(c_972,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1506,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_1498,c_972])).

tff(c_1514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1054,c_973,c_1506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.63  
% 3.54/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.54/1.63  
% 3.54/1.63  %Foreground sorts:
% 3.54/1.63  
% 3.54/1.63  
% 3.54/1.63  %Background operators:
% 3.54/1.63  
% 3.54/1.63  
% 3.54/1.63  %Foreground operators:
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.54/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.54/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.54/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.54/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.54/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.54/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.54/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.54/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.63  
% 3.54/1.65  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 3.54/1.65  tff(f_79, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.54/1.65  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.54/1.65  tff(f_59, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.54/1.65  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.54/1.65  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.54/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.54/1.65  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.54/1.65  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.54/1.65  tff(f_29, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.54/1.65  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.54/1.65  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.54/1.65  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.54/1.65  tff(f_45, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.54/1.65  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.54/1.65  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.65  tff(c_32, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.65  tff(c_1034, plain, (![B_115, A_116]: (r2_hidden(B_115, A_116) | ~m1_subset_1(B_115, A_116) | v1_xboole_0(A_116))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.65  tff(c_20, plain, (![A_19]: (k3_tarski(k1_zfmisc_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.54/1.65  tff(c_107, plain, (![A_38, B_39]: (r1_tarski(A_38, k3_tarski(B_39)) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.54/1.65  tff(c_110, plain, (![A_38, A_19]: (r1_tarski(A_38, A_19) | ~r2_hidden(A_38, k1_zfmisc_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_107])).
% 3.54/1.65  tff(c_1038, plain, (![B_115, A_19]: (r1_tarski(B_115, A_19) | ~m1_subset_1(B_115, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1034, c_110])).
% 3.54/1.65  tff(c_1042, plain, (![B_117, A_118]: (r1_tarski(B_117, A_118) | ~m1_subset_1(B_117, k1_zfmisc_1(A_118)))), inference(negUnitSimplification, [status(thm)], [c_32, c_1038])).
% 3.54/1.65  tff(c_1054, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_1042])).
% 3.54/1.65  tff(c_40, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.65  tff(c_111, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_40])).
% 3.54/1.65  tff(c_311, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.54/1.65  tff(c_323, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_311])).
% 3.54/1.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.54/1.65  tff(c_149, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | ~m1_subset_1(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.54/1.65  tff(c_156, plain, (![B_52, A_19]: (r1_tarski(B_52, A_19) | ~m1_subset_1(B_52, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_149, c_110])).
% 3.54/1.65  tff(c_176, plain, (![B_54, A_55]: (r1_tarski(B_54, A_55) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)))), inference(negUnitSimplification, [status(thm)], [c_32, c_156])).
% 3.54/1.65  tff(c_188, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_176])).
% 3.54/1.65  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.54/1.65  tff(c_193, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_188, c_8])).
% 3.54/1.65  tff(c_214, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_193])).
% 3.54/1.65  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.65  tff(c_279, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_214, c_6])).
% 3.54/1.65  tff(c_369, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_323, c_279])).
% 3.54/1.65  tff(c_112, plain, (![A_40, B_41]: (r1_xboole_0(k3_xboole_0(A_40, B_41), k5_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.54/1.65  tff(c_118, plain, (![A_1, B_2]: (r1_xboole_0(k3_xboole_0(A_1, B_2), k5_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 3.54/1.65  tff(c_201, plain, (r1_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_118])).
% 3.54/1.65  tff(c_370, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_201])).
% 3.54/1.65  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.65  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.65  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.65  tff(c_46, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.54/1.65  tff(c_161, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_111, c_46])).
% 3.54/1.65  tff(c_441, plain, (![C_70, A_71, B_72]: (r1_tarski(C_70, k3_subset_1(A_71, B_72)) | ~r1_tarski(B_72, k3_subset_1(A_71, C_70)) | ~m1_subset_1(C_70, k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.54/1.65  tff(c_445, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_161, c_441])).
% 3.54/1.65  tff(c_451, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_445])).
% 3.54/1.65  tff(c_460, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_451, c_8])).
% 3.54/1.65  tff(c_464, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_460, c_6])).
% 3.54/1.65  tff(c_473, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_464])).
% 3.54/1.65  tff(c_12, plain, (![A_10, B_11, C_12]: (~r1_xboole_0(A_10, k4_xboole_0(B_11, C_12)) | ~r1_xboole_0(A_10, C_12) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.54/1.65  tff(c_481, plain, (![A_10]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r1_xboole_0(A_10, k3_subset_1('#skF_1', '#skF_2')) | r1_xboole_0(A_10, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_473, c_12])).
% 3.54/1.65  tff(c_964, plain, (![A_102]: (~r1_xboole_0(A_102, k3_subset_1('#skF_1', '#skF_2')) | r1_xboole_0(A_102, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_481])).
% 3.54/1.65  tff(c_967, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_370, c_964])).
% 3.54/1.65  tff(c_971, plain, $false, inference(negUnitSimplification, [status(thm)], [c_111, c_967])).
% 3.54/1.65  tff(c_973, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.65  tff(c_1156, plain, (![A_121, B_122]: (k4_xboole_0(A_121, B_122)=k3_subset_1(A_121, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.54/1.65  tff(c_1169, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_1156])).
% 3.54/1.65  tff(c_1219, plain, (![A_126, B_127, C_128]: (r1_tarski(A_126, k4_xboole_0(B_127, C_128)) | ~r1_xboole_0(A_126, C_128) | ~r1_tarski(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.54/1.65  tff(c_1498, plain, (![A_148]: (r1_tarski(A_148, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_148, '#skF_3') | ~r1_tarski(A_148, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1169, c_1219])).
% 3.54/1.65  tff(c_972, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_40])).
% 3.54/1.65  tff(c_1506, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_1498, c_972])).
% 3.54/1.65  tff(c_1514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1054, c_973, c_1506])).
% 3.54/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.65  
% 3.54/1.65  Inference rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Ref     : 0
% 3.54/1.65  #Sup     : 380
% 3.54/1.65  #Fact    : 0
% 3.54/1.65  #Define  : 0
% 3.54/1.65  #Split   : 3
% 3.54/1.65  #Chain   : 0
% 3.54/1.65  #Close   : 0
% 3.54/1.65  
% 3.54/1.65  Ordering : KBO
% 3.54/1.65  
% 3.54/1.65  Simplification rules
% 3.54/1.65  ----------------------
% 3.54/1.65  #Subsume      : 28
% 3.54/1.65  #Demod        : 176
% 3.54/1.65  #Tautology    : 180
% 3.54/1.65  #SimpNegUnit  : 10
% 3.54/1.65  #BackRed      : 5
% 3.54/1.65  
% 3.54/1.65  #Partial instantiations: 0
% 3.54/1.65  #Strategies tried      : 1
% 3.54/1.65  
% 3.54/1.65  Timing (in seconds)
% 3.54/1.65  ----------------------
% 3.54/1.65  Preprocessing        : 0.34
% 3.54/1.65  Parsing              : 0.18
% 3.54/1.65  CNF conversion       : 0.02
% 3.54/1.65  Main loop            : 0.48
% 3.54/1.65  Inferencing          : 0.17
% 3.54/1.65  Reduction            : 0.17
% 3.54/1.65  Demodulation         : 0.12
% 3.54/1.65  BG Simplification    : 0.02
% 3.54/1.65  Subsumption          : 0.07
% 3.54/1.65  Abstraction          : 0.02
% 3.54/1.65  MUC search           : 0.00
% 3.54/1.65  Cooper               : 0.00
% 3.54/1.65  Total                : 0.85
% 3.54/1.65  Index Insertion      : 0.00
% 3.54/1.65  Index Deletion       : 0.00
% 3.54/1.65  Index Matching       : 0.00
% 3.54/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
