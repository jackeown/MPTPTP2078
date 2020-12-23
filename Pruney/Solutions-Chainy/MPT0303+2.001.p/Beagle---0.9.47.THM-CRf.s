%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:50 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 242 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 449 expanded)
%              Number of equality atoms :   27 ( 115 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_208,plain,(
    ! [A_56,B_57,C_58,D_59] :
      ( r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1(C_58,D_59))
      | ~ r2_hidden(B_57,D_59)
      | ~ r2_hidden(A_56,C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_3','#skF_3') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    ! [A_40,C_41,B_42,D_43] :
      ( r2_hidden(A_40,C_41)
      | ~ r2_hidden(k4_tarski(A_40,B_42),k2_zfmisc_1(C_41,D_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_185,plain,(
    ! [A_40,B_42] :
      ( r2_hidden(A_40,'#skF_3')
      | ~ r2_hidden(k4_tarski(A_40,B_42),k2_zfmisc_1('#skF_4','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_182])).

tff(c_228,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,'#skF_3')
      | ~ r2_hidden(B_57,'#skF_4')
      | ~ r2_hidden(A_56,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_208,c_185])).

tff(c_253,plain,(
    ! [B_57] : ~ r2_hidden(B_57,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_233,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(k4_tarski(A_60,B_61),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_61,'#skF_3')
      | ~ r2_hidden(A_60,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_208])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_250,plain,(
    ! [A_60,B_61] :
      ( r2_hidden(A_60,'#skF_4')
      | ~ r2_hidden(B_61,'#skF_3')
      | ~ r2_hidden(A_60,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_233,c_20])).

tff(c_290,plain,(
    ! [B_61,A_60] :
      ( ~ r2_hidden(B_61,'#skF_3')
      | ~ r2_hidden(A_60,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_250])).

tff(c_294,plain,(
    ! [A_63] : ~ r2_hidden(A_63,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_311,plain,(
    ! [B_65] : r1_tarski('#skF_3',B_65) ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_401,plain,(
    ! [B_70] : k3_xboole_0('#skF_3',B_70) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_311,c_12])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_254,plain,(
    ! [B_62] : ~ r2_hidden(B_62,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_278,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10,c_254])).

tff(c_14,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_23] : k3_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_2])).

tff(c_282,plain,(
    ! [A_23] : k3_xboole_0(A_23,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_278,c_74])).

tff(c_406,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_282])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_406])).

tff(c_440,plain,(
    ! [B_71] : ~ r2_hidden(B_71,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_462,plain,(
    ! [B_75] : r1_tarski('#skF_3',B_75) ),
    inference(resolution,[status(thm)],[c_8,c_440])).

tff(c_553,plain,(
    ! [B_83] : k3_xboole_0('#skF_3',B_83) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_462,c_12])).

tff(c_558,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_282])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_558])).

tff(c_590,plain,(
    ! [A_84] :
      ( r2_hidden(A_84,'#skF_3')
      | ~ r2_hidden(A_84,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1072,plain,(
    ! [A_118] :
      ( r1_tarski(A_118,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_118,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_590,c_6])).

tff(c_1088,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1072])).

tff(c_1095,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1088,c_12])).

tff(c_18,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_251,plain,(
    ! [B_61,A_60] :
      ( r2_hidden(B_61,'#skF_4')
      | ~ r2_hidden(B_61,'#skF_3')
      | ~ r2_hidden(A_60,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_233,c_18])).

tff(c_599,plain,(
    ! [A_60] : ~ r2_hidden(A_60,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_589,plain,(
    ! [A_56] :
      ( r2_hidden(A_56,'#skF_3')
      | ~ r2_hidden(A_56,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_639,plain,(
    ! [A_86] : ~ r2_hidden(A_86,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_599,c_589])).

tff(c_655,plain,(
    ! [B_88] : r1_tarski('#skF_4',B_88) ),
    inference(resolution,[status(thm)],[c_8,c_639])).

tff(c_741,plain,(
    ! [B_93] : k3_xboole_0('#skF_4',B_93) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_655,c_12])).

tff(c_603,plain,(
    ! [A_85] : ~ r2_hidden(A_85,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_627,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10,c_603])).

tff(c_631,plain,(
    ! [A_23] : k3_xboole_0(A_23,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_627,c_74])).

tff(c_746,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_631])).

tff(c_776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_746])).

tff(c_778,plain,(
    ! [B_94] :
      ( r2_hidden(B_94,'#skF_4')
      | ~ r2_hidden(B_94,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_993,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_1'('#skF_3',B_109),'#skF_4')
      | r1_tarski('#skF_3',B_109) ) ),
    inference(resolution,[status(thm)],[c_8,c_778])).

tff(c_1001,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_993,c_6])).

tff(c_1008,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1001,c_12])).

tff(c_1019,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_2])).

tff(c_1096,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1095,c_1019])).

tff(c_1098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.38  
% 2.69/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.39  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.69/1.39  
% 2.69/1.39  %Foreground sorts:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Background operators:
% 2.69/1.39  
% 2.69/1.39  
% 2.69/1.39  %Foreground operators:
% 2.69/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.39  
% 2.69/1.40  tff(f_59, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.69/1.40  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.69/1.40  tff(f_54, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.69/1.40  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.69/1.40  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.69/1.40  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.69/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.69/1.40  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.40  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.40  tff(c_208, plain, (![A_56, B_57, C_58, D_59]: (r2_hidden(k4_tarski(A_56, B_57), k2_zfmisc_1(C_58, D_59)) | ~r2_hidden(B_57, D_59) | ~r2_hidden(A_56, C_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.40  tff(c_24, plain, (k2_zfmisc_1('#skF_3', '#skF_3')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.40  tff(c_182, plain, (![A_40, C_41, B_42, D_43]: (r2_hidden(A_40, C_41) | ~r2_hidden(k4_tarski(A_40, B_42), k2_zfmisc_1(C_41, D_43)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.40  tff(c_185, plain, (![A_40, B_42]: (r2_hidden(A_40, '#skF_3') | ~r2_hidden(k4_tarski(A_40, B_42), k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_182])).
% 2.69/1.40  tff(c_228, plain, (![A_56, B_57]: (r2_hidden(A_56, '#skF_3') | ~r2_hidden(B_57, '#skF_4') | ~r2_hidden(A_56, '#skF_4'))), inference(resolution, [status(thm)], [c_208, c_185])).
% 2.69/1.40  tff(c_253, plain, (![B_57]: (~r2_hidden(B_57, '#skF_4'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.69/1.40  tff(c_233, plain, (![A_60, B_61]: (r2_hidden(k4_tarski(A_60, B_61), k2_zfmisc_1('#skF_4', '#skF_4')) | ~r2_hidden(B_61, '#skF_3') | ~r2_hidden(A_60, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_208])).
% 2.69/1.40  tff(c_20, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.40  tff(c_250, plain, (![A_60, B_61]: (r2_hidden(A_60, '#skF_4') | ~r2_hidden(B_61, '#skF_3') | ~r2_hidden(A_60, '#skF_3'))), inference(resolution, [status(thm)], [c_233, c_20])).
% 2.69/1.40  tff(c_290, plain, (![B_61, A_60]: (~r2_hidden(B_61, '#skF_3') | ~r2_hidden(A_60, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_253, c_250])).
% 2.69/1.40  tff(c_294, plain, (![A_63]: (~r2_hidden(A_63, '#skF_3'))), inference(splitLeft, [status(thm)], [c_290])).
% 2.69/1.40  tff(c_311, plain, (![B_65]: (r1_tarski('#skF_3', B_65))), inference(resolution, [status(thm)], [c_8, c_294])).
% 2.69/1.40  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.40  tff(c_401, plain, (![B_70]: (k3_xboole_0('#skF_3', B_70)='#skF_3')), inference(resolution, [status(thm)], [c_311, c_12])).
% 2.69/1.40  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.69/1.40  tff(c_254, plain, (![B_62]: (~r2_hidden(B_62, '#skF_4'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.69/1.40  tff(c_278, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_10, c_254])).
% 2.69/1.40  tff(c_14, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.69/1.40  tff(c_64, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.69/1.40  tff(c_69, plain, (![A_23]: (k3_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_64])).
% 2.69/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.40  tff(c_74, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_69, c_2])).
% 2.69/1.40  tff(c_282, plain, (![A_23]: (k3_xboole_0(A_23, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_278, c_278, c_74])).
% 2.69/1.40  tff(c_406, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_401, c_282])).
% 2.69/1.40  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_406])).
% 2.69/1.40  tff(c_440, plain, (![B_71]: (~r2_hidden(B_71, '#skF_3'))), inference(splitRight, [status(thm)], [c_290])).
% 2.69/1.40  tff(c_462, plain, (![B_75]: (r1_tarski('#skF_3', B_75))), inference(resolution, [status(thm)], [c_8, c_440])).
% 2.69/1.40  tff(c_553, plain, (![B_83]: (k3_xboole_0('#skF_3', B_83)='#skF_3')), inference(resolution, [status(thm)], [c_462, c_12])).
% 2.69/1.40  tff(c_558, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_553, c_282])).
% 2.69/1.40  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_558])).
% 2.69/1.40  tff(c_590, plain, (![A_84]: (r2_hidden(A_84, '#skF_3') | ~r2_hidden(A_84, '#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 2.69/1.40  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.40  tff(c_1072, plain, (![A_118]: (r1_tarski(A_118, '#skF_3') | ~r2_hidden('#skF_1'(A_118, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_590, c_6])).
% 2.69/1.40  tff(c_1088, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_1072])).
% 2.69/1.40  tff(c_1095, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1088, c_12])).
% 2.69/1.40  tff(c_18, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.69/1.40  tff(c_251, plain, (![B_61, A_60]: (r2_hidden(B_61, '#skF_4') | ~r2_hidden(B_61, '#skF_3') | ~r2_hidden(A_60, '#skF_3'))), inference(resolution, [status(thm)], [c_233, c_18])).
% 2.69/1.40  tff(c_599, plain, (![A_60]: (~r2_hidden(A_60, '#skF_3'))), inference(splitLeft, [status(thm)], [c_251])).
% 2.69/1.40  tff(c_589, plain, (![A_56]: (r2_hidden(A_56, '#skF_3') | ~r2_hidden(A_56, '#skF_4'))), inference(splitRight, [status(thm)], [c_228])).
% 2.69/1.40  tff(c_639, plain, (![A_86]: (~r2_hidden(A_86, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_599, c_589])).
% 2.69/1.40  tff(c_655, plain, (![B_88]: (r1_tarski('#skF_4', B_88))), inference(resolution, [status(thm)], [c_8, c_639])).
% 2.69/1.40  tff(c_741, plain, (![B_93]: (k3_xboole_0('#skF_4', B_93)='#skF_4')), inference(resolution, [status(thm)], [c_655, c_12])).
% 2.69/1.40  tff(c_603, plain, (![A_85]: (~r2_hidden(A_85, '#skF_3'))), inference(splitLeft, [status(thm)], [c_251])).
% 2.69/1.40  tff(c_627, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_10, c_603])).
% 2.69/1.40  tff(c_631, plain, (![A_23]: (k3_xboole_0(A_23, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_627, c_627, c_74])).
% 2.69/1.40  tff(c_746, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_741, c_631])).
% 2.69/1.40  tff(c_776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_746])).
% 2.69/1.40  tff(c_778, plain, (![B_94]: (r2_hidden(B_94, '#skF_4') | ~r2_hidden(B_94, '#skF_3'))), inference(splitRight, [status(thm)], [c_251])).
% 2.69/1.40  tff(c_993, plain, (![B_109]: (r2_hidden('#skF_1'('#skF_3', B_109), '#skF_4') | r1_tarski('#skF_3', B_109))), inference(resolution, [status(thm)], [c_8, c_778])).
% 2.69/1.40  tff(c_1001, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_993, c_6])).
% 2.69/1.40  tff(c_1008, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_1001, c_12])).
% 2.69/1.40  tff(c_1019, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1008, c_2])).
% 2.69/1.40  tff(c_1096, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1095, c_1019])).
% 2.69/1.40  tff(c_1098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_1096])).
% 2.69/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  Inference rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Ref     : 0
% 2.69/1.40  #Sup     : 243
% 2.69/1.40  #Fact    : 0
% 2.69/1.40  #Define  : 0
% 2.69/1.40  #Split   : 4
% 2.69/1.40  #Chain   : 0
% 2.69/1.40  #Close   : 0
% 2.69/1.40  
% 2.69/1.40  Ordering : KBO
% 2.69/1.40  
% 2.69/1.40  Simplification rules
% 2.69/1.40  ----------------------
% 2.69/1.40  #Subsume      : 18
% 2.69/1.40  #Demod        : 80
% 2.69/1.40  #Tautology    : 132
% 2.69/1.40  #SimpNegUnit  : 13
% 2.69/1.40  #BackRed      : 29
% 2.69/1.40  
% 2.69/1.40  #Partial instantiations: 0
% 2.69/1.40  #Strategies tried      : 1
% 2.69/1.40  
% 2.69/1.40  Timing (in seconds)
% 2.69/1.40  ----------------------
% 2.69/1.41  Preprocessing        : 0.28
% 2.69/1.41  Parsing              : 0.15
% 2.69/1.41  CNF conversion       : 0.02
% 2.69/1.41  Main loop            : 0.37
% 2.69/1.41  Inferencing          : 0.14
% 2.69/1.41  Reduction            : 0.10
% 2.69/1.41  Demodulation         : 0.07
% 2.69/1.41  BG Simplification    : 0.02
% 2.69/1.41  Subsumption          : 0.07
% 2.69/1.41  Abstraction          : 0.02
% 2.69/1.41  MUC search           : 0.00
% 2.69/1.41  Cooper               : 0.00
% 2.69/1.41  Total                : 0.68
% 2.69/1.41  Index Insertion      : 0.00
% 2.69/1.41  Index Deletion       : 0.00
% 2.69/1.41  Index Matching       : 0.00
% 2.69/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
