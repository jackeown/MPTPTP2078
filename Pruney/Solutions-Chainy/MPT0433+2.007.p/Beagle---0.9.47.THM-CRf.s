%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:14 EST 2020

% Result     : Theorem 18.90s
% Output     : CNFRefutation 18.90s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 439 expanded)
%              Number of leaves         :   30 ( 158 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 655 expanded)
%              Number of equality atoms :   39 ( 266 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_137,plain,(
    ! [B_52,A_53] : k1_setfam_1(k2_tarski(B_52,A_53)) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_70])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_20])).

tff(c_274,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_286,plain,(
    ! [A_62,B_63] : r1_tarski(k3_xboole_0(A_62,B_63),A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_6])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_193,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_9942,plain,(
    ! [A_232,B_233] :
      ( v1_relat_1(A_232)
      | ~ v1_relat_1(B_233)
      | ~ r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_9975,plain,(
    ! [A_234,B_235] :
      ( v1_relat_1(k3_xboole_0(A_234,B_235))
      | ~ v1_relat_1(A_234) ) ),
    inference(resolution,[status(thm)],[c_286,c_9942])).

tff(c_9978,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(k3_xboole_0(B_52,A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_9975])).

tff(c_405,plain,(
    ! [A_77,B_78,C_79] :
      ( r1_tarski(A_77,k3_xboole_0(B_78,C_79))
      | ~ r1_tarski(A_77,C_79)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12044,plain,(
    ! [A_274,B_275,C_276] :
      ( k2_xboole_0(A_274,k3_xboole_0(B_275,C_276)) = k3_xboole_0(B_275,C_276)
      | ~ r1_tarski(A_274,C_276)
      | ~ r1_tarski(A_274,B_275) ) ),
    inference(resolution,[status(thm)],[c_405,c_2])).

tff(c_494,plain,(
    ! [A_84,B_85] :
      ( k2_xboole_0(k1_relat_1(A_84),k1_relat_1(B_85)) = k1_relat_1(k2_xboole_0(A_84,B_85))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_513,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k1_relat_1(A_84),k1_relat_1(k2_xboole_0(A_84,B_85)))
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_10])).

tff(c_12059,plain,(
    ! [A_274,B_275,C_276] :
      ( r1_tarski(k1_relat_1(A_274),k1_relat_1(k3_xboole_0(B_275,C_276)))
      | ~ v1_relat_1(k3_xboole_0(B_275,C_276))
      | ~ v1_relat_1(A_274)
      | ~ r1_tarski(A_274,C_276)
      | ~ r1_tarski(A_274,B_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12044,c_513])).

tff(c_594,plain,(
    ! [A_90,B_91] :
      ( v1_relat_1(A_90)
      | ~ v1_relat_1(B_91)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_623,plain,(
    ! [A_92,B_93] :
      ( v1_relat_1(k3_xboole_0(A_92,B_93))
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_286,c_594])).

tff(c_626,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(k3_xboole_0(B_52,A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_623])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_100,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_198,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(B_59,A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_100])).

tff(c_18,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_204,plain,(
    ! [B_59,A_58] : k2_xboole_0(B_59,A_58) = k2_xboole_0(A_58,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_18])).

tff(c_295,plain,(
    ! [A_64,B_65] : r1_tarski(k3_xboole_0(A_64,B_65),A_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_6])).

tff(c_368,plain,(
    ! [A_75,B_76] : k2_xboole_0(k3_xboole_0(A_75,B_76),A_75) = A_75 ),
    inference(resolution,[status(thm)],[c_295,c_2])).

tff(c_394,plain,(
    ! [A_58,B_76] : k2_xboole_0(A_58,k3_xboole_0(A_58,B_76)) = A_58 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_368])).

tff(c_305,plain,(
    ! [A_64,B_65] : k2_xboole_0(k3_xboole_0(A_64,B_65),A_64) = A_64 ),
    inference(resolution,[status(thm)],[c_295,c_2])).

tff(c_115,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(resolution,[status(thm)],[c_10,c_115])).

tff(c_1832,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(k1_relat_1(A_124),k1_relat_1(k2_xboole_0(A_124,B_125)))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_10])).

tff(c_5201,plain,(
    ! [A_181,B_182] :
      ( r1_tarski(k1_relat_1(A_181),k1_relat_1(k2_xboole_0(A_181,B_182)))
      | ~ v1_relat_1(k2_xboole_0(A_181,B_182))
      | ~ v1_relat_1(A_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_1832])).

tff(c_5267,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_64,B_65)),k1_relat_1(A_64))
      | ~ v1_relat_1(k2_xboole_0(k3_xboole_0(A_64,B_65),A_64))
      | ~ v1_relat_1(k3_xboole_0(A_64,B_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_5201])).

tff(c_9762,plain,(
    ! [A_228,B_229] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_228,B_229)),k1_relat_1(A_228))
      | ~ v1_relat_1(A_228)
      | ~ v1_relat_1(k3_xboole_0(A_228,B_229)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_204,c_5267])).

tff(c_30,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_419,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_405,c_30])).

tff(c_554,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_9771,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9762,c_554])).

tff(c_9855,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9771])).

tff(c_9882,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_626,c_9855])).

tff(c_9889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_9882])).

tff(c_9891,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_122,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_221,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_18])).

tff(c_306,plain,(
    ! [A_66,B_67] : r1_tarski(A_66,k2_xboole_0(B_67,A_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_10])).

tff(c_318,plain,(
    ! [A_6] : r1_tarski(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_306])).

tff(c_470,plain,(
    ! [A_82,B_83] : k2_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = A_82 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_368])).

tff(c_488,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,k3_xboole_0(A_53,B_52)) = B_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_470])).

tff(c_12161,plain,(
    ! [A_53,B_52] :
      ( k3_xboole_0(A_53,B_52) = B_52
      | ~ r1_tarski(B_52,B_52)
      | ~ r1_tarski(B_52,A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_12044])).

tff(c_12725,plain,(
    ! [A_286,B_287] :
      ( k3_xboole_0(A_286,B_287) = B_287
      | ~ r1_tarski(B_287,A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_12161])).

tff(c_12764,plain,(
    k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1(k3_xboole_0('#skF_1','#skF_2'))) = k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9891,c_12725])).

tff(c_12119,plain,(
    ! [B_275,C_276] :
      ( k3_xboole_0(B_275,C_276) = B_275
      | ~ r1_tarski(B_275,C_276)
      | ~ r1_tarski(B_275,B_275) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12044,c_394])).

tff(c_12230,plain,(
    ! [B_277,C_278] :
      ( k3_xboole_0(B_277,C_278) = B_277
      | ~ r1_tarski(B_277,C_278) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_12119])).

tff(c_12267,plain,(
    k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9891,c_12230])).

tff(c_21285,plain,(
    ! [B_378,C_379,A_380] :
      ( k2_xboole_0(k3_xboole_0(B_378,C_379),A_380) = k3_xboole_0(B_378,C_379)
      | ~ r1_tarski(A_380,C_379)
      | ~ r1_tarski(A_380,B_378) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12044,c_204])).

tff(c_21556,plain,(
    ! [A_380] :
      ( k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) = k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),A_380)
      | ~ r1_tarski(A_380,k1_relat_1('#skF_1'))
      | ~ r1_tarski(A_380,k1_relat_1(k3_xboole_0('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12267,c_21285])).

tff(c_21785,plain,(
    ! [A_383] :
      ( k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),A_383) = k1_relat_1(k3_xboole_0('#skF_1','#skF_2'))
      | ~ r1_tarski(A_383,k1_relat_1('#skF_1'))
      | ~ r1_tarski(A_383,k1_relat_1(k3_xboole_0('#skF_1','#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12764,c_143,c_21556])).

tff(c_21815,plain,(
    ! [A_274] :
      ( k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1(A_274)) = k1_relat_1(k3_xboole_0('#skF_1','#skF_2'))
      | ~ r1_tarski(k1_relat_1(A_274),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2'))
      | ~ v1_relat_1(A_274)
      | ~ r1_tarski(A_274,'#skF_2')
      | ~ r1_tarski(A_274,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_12059,c_21785])).

tff(c_23185,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_21815])).

tff(c_23188,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9978,c_23185])).

tff(c_23195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_23188])).

tff(c_23197,plain,(
    v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_21815])).

tff(c_397,plain,(
    ! [B_52,A_53] : k2_xboole_0(k3_xboole_0(B_52,A_53),A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_368])).

tff(c_11603,plain,(
    ! [A_268,B_269] :
      ( r1_tarski(k1_relat_1(A_268),k1_relat_1(k2_xboole_0(A_268,B_269)))
      | ~ v1_relat_1(B_269)
      | ~ v1_relat_1(A_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_10])).

tff(c_53202,plain,(
    ! [B_589,A_590] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_589,A_590)),k1_relat_1(A_590))
      | ~ v1_relat_1(A_590)
      | ~ v1_relat_1(k3_xboole_0(B_589,A_590)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_11603])).

tff(c_9890,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_53221,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_53202,c_9890])).

tff(c_53335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23197,c_32,c_53221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.90/10.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.90/10.65  
% 18.90/10.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.90/10.65  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 18.90/10.65  
% 18.90/10.65  %Foreground sorts:
% 18.90/10.65  
% 18.90/10.65  
% 18.90/10.65  %Background operators:
% 18.90/10.65  
% 18.90/10.65  
% 18.90/10.65  %Foreground operators:
% 18.90/10.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.90/10.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.90/10.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.90/10.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.90/10.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.90/10.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.90/10.65  tff('#skF_2', type, '#skF_2': $i).
% 18.90/10.65  tff('#skF_1', type, '#skF_1': $i).
% 18.90/10.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.90/10.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.90/10.65  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.90/10.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.90/10.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.90/10.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.90/10.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.90/10.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.90/10.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.90/10.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.90/10.65  
% 18.90/10.67  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 18.90/10.67  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 18.90/10.67  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 18.90/10.67  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.90/10.67  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.90/10.67  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.90/10.67  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 18.90/10.67  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 18.90/10.67  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.90/10.67  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 18.90/10.67  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 18.90/10.67  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 18.90/10.67  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.90/10.67  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.90/10.67  tff(c_70, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_137, plain, (![B_52, A_53]: (k1_setfam_1(k2_tarski(B_52, A_53))=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_12, c_70])).
% 18.90/10.67  tff(c_20, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.90/10.67  tff(c_143, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_137, c_20])).
% 18.90/10.67  tff(c_274, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.90/10.67  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.90/10.67  tff(c_286, plain, (![A_62, B_63]: (r1_tarski(k3_xboole_0(A_62, B_63), A_62))), inference(superposition, [status(thm), theory('equality')], [c_274, c_6])).
% 18.90/10.67  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.90/10.67  tff(c_193, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 18.90/10.67  tff(c_9942, plain, (![A_232, B_233]: (v1_relat_1(A_232) | ~v1_relat_1(B_233) | ~r1_tarski(A_232, B_233))), inference(resolution, [status(thm)], [c_24, c_193])).
% 18.90/10.67  tff(c_9975, plain, (![A_234, B_235]: (v1_relat_1(k3_xboole_0(A_234, B_235)) | ~v1_relat_1(A_234))), inference(resolution, [status(thm)], [c_286, c_9942])).
% 18.90/10.67  tff(c_9978, plain, (![B_52, A_53]: (v1_relat_1(k3_xboole_0(B_52, A_53)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_143, c_9975])).
% 18.90/10.67  tff(c_405, plain, (![A_77, B_78, C_79]: (r1_tarski(A_77, k3_xboole_0(B_78, C_79)) | ~r1_tarski(A_77, C_79) | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.90/10.67  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.90/10.67  tff(c_12044, plain, (![A_274, B_275, C_276]: (k2_xboole_0(A_274, k3_xboole_0(B_275, C_276))=k3_xboole_0(B_275, C_276) | ~r1_tarski(A_274, C_276) | ~r1_tarski(A_274, B_275))), inference(resolution, [status(thm)], [c_405, c_2])).
% 18.90/10.67  tff(c_494, plain, (![A_84, B_85]: (k2_xboole_0(k1_relat_1(A_84), k1_relat_1(B_85))=k1_relat_1(k2_xboole_0(A_84, B_85)) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.90/10.67  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.90/10.67  tff(c_513, plain, (![A_84, B_85]: (r1_tarski(k1_relat_1(A_84), k1_relat_1(k2_xboole_0(A_84, B_85))) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_494, c_10])).
% 18.90/10.67  tff(c_12059, plain, (![A_274, B_275, C_276]: (r1_tarski(k1_relat_1(A_274), k1_relat_1(k3_xboole_0(B_275, C_276))) | ~v1_relat_1(k3_xboole_0(B_275, C_276)) | ~v1_relat_1(A_274) | ~r1_tarski(A_274, C_276) | ~r1_tarski(A_274, B_275))), inference(superposition, [status(thm), theory('equality')], [c_12044, c_513])).
% 18.90/10.67  tff(c_594, plain, (![A_90, B_91]: (v1_relat_1(A_90) | ~v1_relat_1(B_91) | ~r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_24, c_193])).
% 18.90/10.67  tff(c_623, plain, (![A_92, B_93]: (v1_relat_1(k3_xboole_0(A_92, B_93)) | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_286, c_594])).
% 18.90/10.67  tff(c_626, plain, (![B_52, A_53]: (v1_relat_1(k3_xboole_0(B_52, A_53)) | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_143, c_623])).
% 18.90/10.67  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.90/10.67  tff(c_100, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.90/10.67  tff(c_198, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(B_59, A_58))), inference(superposition, [status(thm), theory('equality')], [c_12, c_100])).
% 18.90/10.67  tff(c_18, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 18.90/10.67  tff(c_204, plain, (![B_59, A_58]: (k2_xboole_0(B_59, A_58)=k2_xboole_0(A_58, B_59))), inference(superposition, [status(thm), theory('equality')], [c_198, c_18])).
% 18.90/10.67  tff(c_295, plain, (![A_64, B_65]: (r1_tarski(k3_xboole_0(A_64, B_65), A_64))), inference(superposition, [status(thm), theory('equality')], [c_274, c_6])).
% 18.90/10.67  tff(c_368, plain, (![A_75, B_76]: (k2_xboole_0(k3_xboole_0(A_75, B_76), A_75)=A_75)), inference(resolution, [status(thm)], [c_295, c_2])).
% 18.90/10.67  tff(c_394, plain, (![A_58, B_76]: (k2_xboole_0(A_58, k3_xboole_0(A_58, B_76))=A_58)), inference(superposition, [status(thm), theory('equality')], [c_204, c_368])).
% 18.90/10.67  tff(c_305, plain, (![A_64, B_65]: (k2_xboole_0(k3_xboole_0(A_64, B_65), A_64)=A_64)), inference(resolution, [status(thm)], [c_295, c_2])).
% 18.90/10.67  tff(c_115, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.90/10.67  tff(c_123, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(resolution, [status(thm)], [c_10, c_115])).
% 18.90/10.67  tff(c_1832, plain, (![A_124, B_125]: (r1_tarski(k1_relat_1(A_124), k1_relat_1(k2_xboole_0(A_124, B_125))) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_494, c_10])).
% 18.90/10.67  tff(c_5201, plain, (![A_181, B_182]: (r1_tarski(k1_relat_1(A_181), k1_relat_1(k2_xboole_0(A_181, B_182))) | ~v1_relat_1(k2_xboole_0(A_181, B_182)) | ~v1_relat_1(A_181))), inference(superposition, [status(thm), theory('equality')], [c_123, c_1832])).
% 18.90/10.67  tff(c_5267, plain, (![A_64, B_65]: (r1_tarski(k1_relat_1(k3_xboole_0(A_64, B_65)), k1_relat_1(A_64)) | ~v1_relat_1(k2_xboole_0(k3_xboole_0(A_64, B_65), A_64)) | ~v1_relat_1(k3_xboole_0(A_64, B_65)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_5201])).
% 18.90/10.67  tff(c_9762, plain, (![A_228, B_229]: (r1_tarski(k1_relat_1(k3_xboole_0(A_228, B_229)), k1_relat_1(A_228)) | ~v1_relat_1(A_228) | ~v1_relat_1(k3_xboole_0(A_228, B_229)))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_204, c_5267])).
% 18.90/10.67  tff(c_30, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 18.90/10.67  tff(c_419, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_405, c_30])).
% 18.90/10.67  tff(c_554, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_419])).
% 18.90/10.67  tff(c_9771, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_9762, c_554])).
% 18.90/10.67  tff(c_9855, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_9771])).
% 18.90/10.67  tff(c_9882, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_626, c_9855])).
% 18.90/10.67  tff(c_9889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_9882])).
% 18.90/10.67  tff(c_9891, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_419])).
% 18.90/10.67  tff(c_122, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_6, c_115])).
% 18.90/10.67  tff(c_221, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_198, c_18])).
% 18.90/10.67  tff(c_306, plain, (![A_66, B_67]: (r1_tarski(A_66, k2_xboole_0(B_67, A_66)))), inference(superposition, [status(thm), theory('equality')], [c_221, c_10])).
% 18.90/10.67  tff(c_318, plain, (![A_6]: (r1_tarski(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_122, c_306])).
% 18.90/10.67  tff(c_470, plain, (![A_82, B_83]: (k2_xboole_0(A_82, k3_xboole_0(A_82, B_83))=A_82)), inference(superposition, [status(thm), theory('equality')], [c_204, c_368])).
% 18.90/10.67  tff(c_488, plain, (![B_52, A_53]: (k2_xboole_0(B_52, k3_xboole_0(A_53, B_52))=B_52)), inference(superposition, [status(thm), theory('equality')], [c_143, c_470])).
% 18.90/10.67  tff(c_12161, plain, (![A_53, B_52]: (k3_xboole_0(A_53, B_52)=B_52 | ~r1_tarski(B_52, B_52) | ~r1_tarski(B_52, A_53))), inference(superposition, [status(thm), theory('equality')], [c_488, c_12044])).
% 18.90/10.67  tff(c_12725, plain, (![A_286, B_287]: (k3_xboole_0(A_286, B_287)=B_287 | ~r1_tarski(B_287, A_286))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_12161])).
% 18.90/10.67  tff(c_12764, plain, (k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')))=k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_9891, c_12725])).
% 18.90/10.67  tff(c_12119, plain, (![B_275, C_276]: (k3_xboole_0(B_275, C_276)=B_275 | ~r1_tarski(B_275, C_276) | ~r1_tarski(B_275, B_275))), inference(superposition, [status(thm), theory('equality')], [c_12044, c_394])).
% 18.90/10.67  tff(c_12230, plain, (![B_277, C_278]: (k3_xboole_0(B_277, C_278)=B_277 | ~r1_tarski(B_277, C_278))), inference(demodulation, [status(thm), theory('equality')], [c_318, c_12119])).
% 18.90/10.67  tff(c_12267, plain, (k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_9891, c_12230])).
% 18.90/10.67  tff(c_21285, plain, (![B_378, C_379, A_380]: (k2_xboole_0(k3_xboole_0(B_378, C_379), A_380)=k3_xboole_0(B_378, C_379) | ~r1_tarski(A_380, C_379) | ~r1_tarski(A_380, B_378))), inference(superposition, [status(thm), theory('equality')], [c_12044, c_204])).
% 18.90/10.67  tff(c_21556, plain, (![A_380]: (k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))=k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), A_380) | ~r1_tarski(A_380, k1_relat_1('#skF_1')) | ~r1_tarski(A_380, k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_12267, c_21285])).
% 18.90/10.67  tff(c_21785, plain, (![A_383]: (k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), A_383)=k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(A_383, k1_relat_1('#skF_1')) | ~r1_tarski(A_383, k1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12764, c_143, c_21556])).
% 18.90/10.67  tff(c_21815, plain, (![A_274]: (k2_xboole_0(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1(A_274))=k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1(A_274), k1_relat_1('#skF_1')) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(A_274) | ~r1_tarski(A_274, '#skF_2') | ~r1_tarski(A_274, '#skF_1'))), inference(resolution, [status(thm)], [c_12059, c_21785])).
% 18.90/10.67  tff(c_23185, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_21815])).
% 18.90/10.67  tff(c_23188, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9978, c_23185])).
% 18.90/10.67  tff(c_23195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_23188])).
% 18.90/10.67  tff(c_23197, plain, (v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_21815])).
% 18.90/10.67  tff(c_397, plain, (![B_52, A_53]: (k2_xboole_0(k3_xboole_0(B_52, A_53), A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_143, c_368])).
% 18.90/10.67  tff(c_11603, plain, (![A_268, B_269]: (r1_tarski(k1_relat_1(A_268), k1_relat_1(k2_xboole_0(A_268, B_269))) | ~v1_relat_1(B_269) | ~v1_relat_1(A_268))), inference(superposition, [status(thm), theory('equality')], [c_494, c_10])).
% 18.90/10.67  tff(c_53202, plain, (![B_589, A_590]: (r1_tarski(k1_relat_1(k3_xboole_0(B_589, A_590)), k1_relat_1(A_590)) | ~v1_relat_1(A_590) | ~v1_relat_1(k3_xboole_0(B_589, A_590)))), inference(superposition, [status(thm), theory('equality')], [c_397, c_11603])).
% 18.90/10.67  tff(c_9890, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_419])).
% 18.90/10.67  tff(c_53221, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_53202, c_9890])).
% 18.90/10.67  tff(c_53335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23197, c_32, c_53221])).
% 18.90/10.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.90/10.67  
% 18.90/10.67  Inference rules
% 18.90/10.67  ----------------------
% 18.90/10.67  #Ref     : 0
% 18.90/10.67  #Sup     : 13539
% 18.90/10.67  #Fact    : 0
% 18.90/10.67  #Define  : 0
% 18.90/10.67  #Split   : 7
% 18.90/10.67  #Chain   : 0
% 18.90/10.67  #Close   : 0
% 18.90/10.67  
% 18.90/10.67  Ordering : KBO
% 18.90/10.67  
% 18.90/10.67  Simplification rules
% 18.90/10.67  ----------------------
% 18.90/10.67  #Subsume      : 3038
% 18.90/10.67  #Demod        : 21251
% 18.90/10.67  #Tautology    : 6758
% 18.90/10.67  #SimpNegUnit  : 17
% 18.90/10.67  #BackRed      : 7
% 18.90/10.67  
% 18.90/10.67  #Partial instantiations: 0
% 18.90/10.67  #Strategies tried      : 1
% 18.90/10.67  
% 18.90/10.67  Timing (in seconds)
% 18.90/10.67  ----------------------
% 18.90/10.67  Preprocessing        : 0.30
% 18.90/10.67  Parsing              : 0.16
% 18.90/10.67  CNF conversion       : 0.02
% 18.90/10.67  Main loop            : 9.59
% 18.90/10.67  Inferencing          : 1.31
% 18.90/10.67  Reduction            : 6.00
% 18.90/10.67  Demodulation         : 5.52
% 18.90/10.67  BG Simplification    : 0.15
% 18.90/10.67  Subsumption          : 1.84
% 18.90/10.67  Abstraction          : 0.36
% 18.90/10.67  MUC search           : 0.00
% 18.90/10.67  Cooper               : 0.00
% 18.90/10.67  Total                : 9.93
% 18.90/10.67  Index Insertion      : 0.00
% 18.90/10.67  Index Deletion       : 0.00
% 18.90/10.67  Index Matching       : 0.00
% 18.90/10.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
