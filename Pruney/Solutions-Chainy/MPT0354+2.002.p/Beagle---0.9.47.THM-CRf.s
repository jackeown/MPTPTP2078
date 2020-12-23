%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 39.85s
% Output     : CNFRefutation 39.85s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 234 expanded)
%              Number of leaves         :   33 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 357 expanded)
%              Number of equality atoms :   60 ( 147 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k3_subset_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1745,plain,(
    ! [A_119,B_120,C_121] :
      ( k4_subset_1(A_119,B_120,C_121) = k2_xboole_0(B_120,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(A_119))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1935,plain,(
    ! [B_126] :
      ( k4_subset_1('#skF_2',B_126,'#skF_4') = k2_xboole_0(B_126,'#skF_4')
      | ~ m1_subset_1(B_126,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1745])).

tff(c_1985,plain,(
    ! [B_23] :
      ( k4_subset_1('#skF_2',k3_subset_1('#skF_2',B_23),'#skF_4') = k2_xboole_0(k3_subset_1('#skF_2',B_23),'#skF_4')
      | ~ m1_subset_1(B_23,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_22,c_1935])).

tff(c_20833,plain,(
    ! [B_354] :
      ( k4_subset_1('#skF_2',k3_subset_1('#skF_2',B_354),'#skF_4') = k2_xboole_0('#skF_4',k3_subset_1('#skF_2',B_354))
      | ~ m1_subset_1(B_354,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1985])).

tff(c_20949,plain,(
    k4_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3'),'#skF_4') = k2_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_20833])).

tff(c_869,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_subset_1(A_94,B_95,C_96) = k4_xboole_0(B_95,C_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_900,plain,(
    ! [C_96] : k7_subset_1('#skF_2','#skF_3',C_96) = k4_xboole_0('#skF_3',C_96) ),
    inference(resolution,[status(thm)],[c_38,c_869])).

tff(c_34,plain,(
    k4_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3'),'#skF_4') != k3_subset_1('#skF_2',k7_subset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_936,plain,(
    k4_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3'),'#skF_4') != k3_subset_1('#skF_2',k4_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_34])).

tff(c_22142,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_3','#skF_4')) != k2_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20949,c_936])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_113,plain,(
    ! [A_51] : r1_tarski(A_51,A_51) ),
    inference(resolution,[status(thm)],[c_107,c_8])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_117,plain,(
    ! [A_51] : k3_xboole_0(A_51,A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_113,c_12])).

tff(c_164,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k4_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_184,plain,(
    ! [A_51,C_67] : k3_xboole_0(A_51,k4_xboole_0(A_51,C_67)) = k4_xboole_0(A_51,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_164])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_687,plain,(
    ! [A_84,B_85,C_86] :
      ( k9_subset_1(A_84,B_85,C_86) = k3_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_772,plain,(
    ! [B_90] : k9_subset_1('#skF_2',B_90,'#skF_3') = k3_xboole_0(B_90,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_687])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1(k9_subset_1(A_24,B_25,C_26),k1_zfmisc_1(A_24))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_778,plain,(
    ! [B_90] :
      ( m1_subset_1(k3_xboole_0(B_90,'#skF_3'),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_24])).

tff(c_786,plain,(
    ! [B_91] : m1_subset_1(k3_xboole_0(B_91,'#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_778])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = k3_subset_1(A_20,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_805,plain,(
    ! [B_91] : k4_xboole_0('#skF_2',k3_xboole_0(B_91,'#skF_3')) = k3_subset_1('#skF_2',k3_xboole_0(B_91,'#skF_3')) ),
    inference(resolution,[status(thm)],[c_786,c_20])).

tff(c_151,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = k3_subset_1(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_151])).

tff(c_1194,plain,(
    ! [A_105,B_106,C_107] : k2_xboole_0(k4_xboole_0(A_105,B_106),k4_xboole_0(A_105,C_107)) = k4_xboole_0(A_105,k3_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1248,plain,(
    ! [B_106] : k2_xboole_0(k4_xboole_0('#skF_2',B_106),k3_subset_1('#skF_2','#skF_3')) = k4_xboole_0('#skF_2',k3_xboole_0(B_106,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_1194])).

tff(c_14209,plain,(
    ! [B_106] : k2_xboole_0(k4_xboole_0('#skF_2',B_106),k3_subset_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k3_xboole_0(B_106,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_1248])).

tff(c_2757,plain,(
    ! [A_144,C_145,B_146] : k2_xboole_0(k4_xboole_0(A_144,C_145),k4_xboole_0(A_144,B_146)) = k4_xboole_0(A_144,k3_xboole_0(B_146,C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_2])).

tff(c_2817,plain,(
    ! [C_145] : k2_xboole_0(k4_xboole_0('#skF_2',C_145),k3_subset_1('#skF_2','#skF_3')) = k4_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_145)) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2757])).

tff(c_35076,plain,(
    ! [C_525] : k4_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_525)) = k3_subset_1('#skF_2',k3_xboole_0(C_525,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14209,c_2817])).

tff(c_35325,plain,(
    ! [C_67] : k3_subset_1('#skF_2',k3_xboole_0(k4_xboole_0('#skF_3',C_67),'#skF_3')) = k4_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_35076])).

tff(c_35384,plain,(
    ! [C_67] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_67)) = k3_subset_1('#skF_2',k4_xboole_0('#skF_3',C_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_4,c_35325])).

tff(c_162,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_151])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4156,plain,(
    ! [A_159,B_160,A_161] :
      ( r2_hidden('#skF_1'(A_159,B_160),A_161)
      | ~ m1_subset_1(A_159,k1_zfmisc_1(A_161))
      | r1_tarski(A_159,B_160) ) ),
    inference(resolution,[status(thm)],[c_10,c_147])).

tff(c_4168,plain,(
    ! [A_162,A_163] :
      ( ~ m1_subset_1(A_162,k1_zfmisc_1(A_163))
      | r1_tarski(A_162,A_163) ) ),
    inference(resolution,[status(thm)],[c_4156,c_8])).

tff(c_4264,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_4168])).

tff(c_4272,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4264,c_12])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8684,plain,(
    ! [C_234] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_2',C_234)) = k4_xboole_0('#skF_3',C_234) ),
    inference(superposition,[status(thm),theory(equality)],[c_4272,c_16])).

tff(c_8776,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_8684])).

tff(c_4263,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_4168])).

tff(c_4268,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4263,c_12])).

tff(c_225,plain,(
    ! [A_68,C_69] : k3_xboole_0(A_68,k4_xboole_0(A_68,C_69)) = k4_xboole_0(A_68,C_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_164])).

tff(c_243,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_225])).

tff(c_257,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_243])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_198,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_14])).

tff(c_201,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = k3_xboole_0('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_198])).

tff(c_4276,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4268,c_201])).

tff(c_187,plain,(
    ! [B_4,A_3,C_67] : k4_xboole_0(k3_xboole_0(B_4,A_3),C_67) = k3_xboole_0(A_3,k4_xboole_0(B_4,C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_164])).

tff(c_2790,plain,(
    ! [A_3,B_4,C_67,B_146] : k2_xboole_0(k3_xboole_0(A_3,k4_xboole_0(B_4,C_67)),k4_xboole_0(k3_xboole_0(B_4,A_3),B_146)) = k4_xboole_0(k3_xboole_0(B_4,A_3),k3_xboole_0(B_146,C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_2757])).

tff(c_27400,plain,(
    ! [A_449,B_450,C_451,B_452] : k2_xboole_0(k3_xboole_0(A_449,k4_xboole_0(B_450,C_451)),k3_xboole_0(B_450,k4_xboole_0(A_449,B_452))) = k3_xboole_0(B_450,k4_xboole_0(A_449,k3_xboole_0(B_452,C_451))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_2790])).

tff(c_101304,plain,(
    ! [A_856,B_857] : k2_xboole_0(k3_xboole_0(A_856,k3_subset_1('#skF_2','#skF_3')),k3_xboole_0('#skF_2',k4_xboole_0(A_856,B_857))) = k3_xboole_0('#skF_2',k4_xboole_0(A_856,k3_xboole_0(B_857,'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_27400])).

tff(c_101512,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k3_xboole_0(k3_subset_1('#skF_2','#skF_4'),'#skF_3'))) = k2_xboole_0(k3_xboole_0('#skF_2',k3_subset_1('#skF_2','#skF_3')),k3_xboole_0('#skF_2','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4276,c_101304])).

tff(c_101662,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35384,c_8776,c_2,c_4268,c_2,c_257,c_184,c_2,c_4,c_4,c_101512])).

tff(c_101664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22142,c_101662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.85/30.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.85/30.23  
% 39.85/30.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.85/30.23  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 39.85/30.23  
% 39.85/30.23  %Foreground sorts:
% 39.85/30.23  
% 39.85/30.23  
% 39.85/30.23  %Background operators:
% 39.85/30.23  
% 39.85/30.23  
% 39.85/30.23  %Foreground operators:
% 39.85/30.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.85/30.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.85/30.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.85/30.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.85/30.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 39.85/30.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 39.85/30.23  tff('#skF_2', type, '#skF_2': $i).
% 39.85/30.23  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 39.85/30.23  tff('#skF_3', type, '#skF_3': $i).
% 39.85/30.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.85/30.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.85/30.23  tff('#skF_4', type, '#skF_4': $i).
% 39.85/30.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.85/30.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.85/30.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.85/30.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 39.85/30.23  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 39.85/30.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 39.85/30.23  
% 39.85/30.25  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 39.85/30.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 39.85/30.25  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 39.85/30.25  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 39.85/30.25  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 39.85/30.25  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 39.85/30.25  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 39.85/30.25  tff(f_44, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 39.85/30.25  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 39.85/30.25  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 39.85/30.25  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 39.85/30.25  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 39.85/30.25  tff(f_46, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_xboole_1)).
% 39.85/30.25  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 39.85/30.25  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 39.85/30.25  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 39.85/30.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.85/30.25  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(k3_subset_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 39.85/30.25  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 39.85/30.25  tff(c_1745, plain, (![A_119, B_120, C_121]: (k4_subset_1(A_119, B_120, C_121)=k2_xboole_0(B_120, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(A_119)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 39.85/30.25  tff(c_1935, plain, (![B_126]: (k4_subset_1('#skF_2', B_126, '#skF_4')=k2_xboole_0(B_126, '#skF_4') | ~m1_subset_1(B_126, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_1745])).
% 39.85/30.25  tff(c_1985, plain, (![B_23]: (k4_subset_1('#skF_2', k3_subset_1('#skF_2', B_23), '#skF_4')=k2_xboole_0(k3_subset_1('#skF_2', B_23), '#skF_4') | ~m1_subset_1(B_23, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_22, c_1935])).
% 39.85/30.25  tff(c_20833, plain, (![B_354]: (k4_subset_1('#skF_2', k3_subset_1('#skF_2', B_354), '#skF_4')=k2_xboole_0('#skF_4', k3_subset_1('#skF_2', B_354)) | ~m1_subset_1(B_354, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1985])).
% 39.85/30.25  tff(c_20949, plain, (k4_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'), '#skF_4')=k2_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_20833])).
% 39.85/30.25  tff(c_869, plain, (![A_94, B_95, C_96]: (k7_subset_1(A_94, B_95, C_96)=k4_xboole_0(B_95, C_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 39.85/30.25  tff(c_900, plain, (![C_96]: (k7_subset_1('#skF_2', '#skF_3', C_96)=k4_xboole_0('#skF_3', C_96))), inference(resolution, [status(thm)], [c_38, c_869])).
% 39.85/30.25  tff(c_34, plain, (k4_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'), '#skF_4')!=k3_subset_1('#skF_2', k7_subset_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 39.85/30.25  tff(c_936, plain, (k4_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'), '#skF_4')!=k3_subset_1('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_900, c_34])).
% 39.85/30.25  tff(c_22142, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))!=k2_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20949, c_936])).
% 39.85/30.25  tff(c_107, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_36])).
% 39.85/30.25  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 39.85/30.25  tff(c_113, plain, (![A_51]: (r1_tarski(A_51, A_51))), inference(resolution, [status(thm)], [c_107, c_8])).
% 39.85/30.25  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 39.85/30.25  tff(c_117, plain, (![A_51]: (k3_xboole_0(A_51, A_51)=A_51)), inference(resolution, [status(thm)], [c_113, c_12])).
% 39.85/30.25  tff(c_164, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k4_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 39.85/30.25  tff(c_184, plain, (![A_51, C_67]: (k3_xboole_0(A_51, k4_xboole_0(A_51, C_67))=k4_xboole_0(A_51, C_67))), inference(superposition, [status(thm), theory('equality')], [c_117, c_164])).
% 39.85/30.25  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.85/30.25  tff(c_687, plain, (![A_84, B_85, C_86]: (k9_subset_1(A_84, B_85, C_86)=k3_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 39.85/30.25  tff(c_772, plain, (![B_90]: (k9_subset_1('#skF_2', B_90, '#skF_3')=k3_xboole_0(B_90, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_687])).
% 39.85/30.25  tff(c_24, plain, (![A_24, B_25, C_26]: (m1_subset_1(k9_subset_1(A_24, B_25, C_26), k1_zfmisc_1(A_24)) | ~m1_subset_1(C_26, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 39.85/30.25  tff(c_778, plain, (![B_90]: (m1_subset_1(k3_xboole_0(B_90, '#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_772, c_24])).
% 39.85/30.25  tff(c_786, plain, (![B_91]: (m1_subset_1(k3_xboole_0(B_91, '#skF_3'), k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_778])).
% 39.85/30.25  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=k3_subset_1(A_20, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 39.85/30.25  tff(c_805, plain, (![B_91]: (k4_xboole_0('#skF_2', k3_xboole_0(B_91, '#skF_3'))=k3_subset_1('#skF_2', k3_xboole_0(B_91, '#skF_3')))), inference(resolution, [status(thm)], [c_786, c_20])).
% 39.85/30.25  tff(c_151, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=k3_subset_1(A_63, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 39.85/30.25  tff(c_163, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_151])).
% 39.85/30.25  tff(c_1194, plain, (![A_105, B_106, C_107]: (k2_xboole_0(k4_xboole_0(A_105, B_106), k4_xboole_0(A_105, C_107))=k4_xboole_0(A_105, k3_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 39.85/30.25  tff(c_1248, plain, (![B_106]: (k2_xboole_0(k4_xboole_0('#skF_2', B_106), k3_subset_1('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', k3_xboole_0(B_106, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_163, c_1194])).
% 39.85/30.25  tff(c_14209, plain, (![B_106]: (k2_xboole_0(k4_xboole_0('#skF_2', B_106), k3_subset_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k3_xboole_0(B_106, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_1248])).
% 39.85/30.25  tff(c_2757, plain, (![A_144, C_145, B_146]: (k2_xboole_0(k4_xboole_0(A_144, C_145), k4_xboole_0(A_144, B_146))=k4_xboole_0(A_144, k3_xboole_0(B_146, C_145)))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_2])).
% 39.85/30.25  tff(c_2817, plain, (![C_145]: (k2_xboole_0(k4_xboole_0('#skF_2', C_145), k3_subset_1('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_145)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2757])).
% 39.85/30.25  tff(c_35076, plain, (![C_525]: (k4_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_525))=k3_subset_1('#skF_2', k3_xboole_0(C_525, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14209, c_2817])).
% 39.85/30.25  tff(c_35325, plain, (![C_67]: (k3_subset_1('#skF_2', k3_xboole_0(k4_xboole_0('#skF_3', C_67), '#skF_3'))=k4_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_67)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_35076])).
% 39.85/30.25  tff(c_35384, plain, (![C_67]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_67))=k3_subset_1('#skF_2', k4_xboole_0('#skF_3', C_67)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_4, c_35325])).
% 39.85/30.25  tff(c_162, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_36, c_151])).
% 39.85/30.25  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 39.85/30.25  tff(c_147, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 39.85/30.25  tff(c_4156, plain, (![A_159, B_160, A_161]: (r2_hidden('#skF_1'(A_159, B_160), A_161) | ~m1_subset_1(A_159, k1_zfmisc_1(A_161)) | r1_tarski(A_159, B_160))), inference(resolution, [status(thm)], [c_10, c_147])).
% 39.85/30.25  tff(c_4168, plain, (![A_162, A_163]: (~m1_subset_1(A_162, k1_zfmisc_1(A_163)) | r1_tarski(A_162, A_163))), inference(resolution, [status(thm)], [c_4156, c_8])).
% 39.85/30.25  tff(c_4264, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_4168])).
% 39.85/30.25  tff(c_4272, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_4264, c_12])).
% 39.85/30.25  tff(c_16, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 39.85/30.25  tff(c_8684, plain, (![C_234]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_2', C_234))=k4_xboole_0('#skF_3', C_234))), inference(superposition, [status(thm), theory('equality')], [c_4272, c_16])).
% 39.85/30.25  tff(c_8776, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_8684])).
% 39.85/30.25  tff(c_4263, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_4168])).
% 39.85/30.25  tff(c_4268, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_4263, c_12])).
% 39.85/30.25  tff(c_225, plain, (![A_68, C_69]: (k3_xboole_0(A_68, k4_xboole_0(A_68, C_69))=k4_xboole_0(A_68, C_69))), inference(superposition, [status(thm), theory('equality')], [c_117, c_164])).
% 39.85/30.25  tff(c_243, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_163, c_225])).
% 39.85/30.25  tff(c_257, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_243])).
% 39.85/30.25  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 39.85/30.25  tff(c_198, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_14])).
% 39.85/30.25  tff(c_201, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_198])).
% 39.85/30.25  tff(c_4276, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4268, c_201])).
% 39.85/30.25  tff(c_187, plain, (![B_4, A_3, C_67]: (k4_xboole_0(k3_xboole_0(B_4, A_3), C_67)=k3_xboole_0(A_3, k4_xboole_0(B_4, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_164])).
% 39.85/30.25  tff(c_2790, plain, (![A_3, B_4, C_67, B_146]: (k2_xboole_0(k3_xboole_0(A_3, k4_xboole_0(B_4, C_67)), k4_xboole_0(k3_xboole_0(B_4, A_3), B_146))=k4_xboole_0(k3_xboole_0(B_4, A_3), k3_xboole_0(B_146, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_187, c_2757])).
% 39.85/30.25  tff(c_27400, plain, (![A_449, B_450, C_451, B_452]: (k2_xboole_0(k3_xboole_0(A_449, k4_xboole_0(B_450, C_451)), k3_xboole_0(B_450, k4_xboole_0(A_449, B_452)))=k3_xboole_0(B_450, k4_xboole_0(A_449, k3_xboole_0(B_452, C_451))))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_2790])).
% 39.85/30.25  tff(c_101304, plain, (![A_856, B_857]: (k2_xboole_0(k3_xboole_0(A_856, k3_subset_1('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', k4_xboole_0(A_856, B_857)))=k3_xboole_0('#skF_2', k4_xboole_0(A_856, k3_xboole_0(B_857, '#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_163, c_27400])).
% 39.85/30.25  tff(c_101512, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k3_xboole_0(k3_subset_1('#skF_2', '#skF_4'), '#skF_3')))=k2_xboole_0(k3_xboole_0('#skF_2', k3_subset_1('#skF_2', '#skF_3')), k3_xboole_0('#skF_2', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4276, c_101304])).
% 39.85/30.25  tff(c_101662, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_35384, c_8776, c_2, c_4268, c_2, c_257, c_184, c_2, c_4, c_4, c_101512])).
% 39.85/30.25  tff(c_101664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22142, c_101662])).
% 39.85/30.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.85/30.25  
% 39.85/30.25  Inference rules
% 39.85/30.25  ----------------------
% 39.85/30.25  #Ref     : 0
% 39.85/30.25  #Sup     : 24672
% 39.85/30.25  #Fact    : 0
% 39.85/30.25  #Define  : 0
% 39.85/30.25  #Split   : 0
% 39.85/30.25  #Chain   : 0
% 39.85/30.25  #Close   : 0
% 39.85/30.25  
% 39.85/30.25  Ordering : KBO
% 39.85/30.25  
% 39.85/30.25  Simplification rules
% 39.85/30.25  ----------------------
% 39.85/30.25  #Subsume      : 526
% 39.85/30.25  #Demod        : 37066
% 39.85/30.25  #Tautology    : 9746
% 39.85/30.25  #SimpNegUnit  : 1
% 39.85/30.25  #BackRed      : 85
% 39.85/30.25  
% 39.85/30.25  #Partial instantiations: 0
% 39.85/30.25  #Strategies tried      : 1
% 39.85/30.25  
% 39.85/30.25  Timing (in seconds)
% 39.85/30.25  ----------------------
% 39.85/30.25  Preprocessing        : 0.32
% 39.85/30.25  Parsing              : 0.17
% 39.85/30.25  CNF conversion       : 0.02
% 39.85/30.25  Main loop            : 29.15
% 39.85/30.25  Inferencing          : 2.75
% 39.85/30.25  Reduction            : 21.00
% 39.85/30.25  Demodulation         : 19.81
% 39.85/30.25  BG Simplification    : 0.50
% 39.85/30.25  Subsumption          : 4.02
% 39.85/30.25  Abstraction          : 0.82
% 39.85/30.25  MUC search           : 0.00
% 39.85/30.25  Cooper               : 0.00
% 39.85/30.25  Total                : 29.51
% 39.85/30.25  Index Insertion      : 0.00
% 39.85/30.25  Index Deletion       : 0.00
% 39.85/30.25  Index Matching       : 0.00
% 39.85/30.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
