%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:52 EST 2020

% Result     : Theorem 11.74s
% Output     : CNFRefutation 11.74s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 155 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  115 ( 222 expanded)
%              Number of equality atoms :   47 ( 100 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_85,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_64,plain,(
    m1_subset_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_156,plain,(
    ! [B_54,A_55] :
      ( v1_xboole_0(B_54)
      | ~ m1_subset_1(B_54,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_168,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_156])).

tff(c_169,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( r2_hidden(B_30,A_29)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_21] : k5_xboole_0(A_21,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [A_67,B_68] : k5_xboole_0(k5_xboole_0(A_67,B_68),k2_xboole_0(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_277,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_235])).

tff(c_283,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32,c_277])).

tff(c_390,plain,(
    ! [A_71,B_72,C_73] : k5_xboole_0(k5_xboole_0(A_71,B_72),C_73) = k5_xboole_0(A_71,k5_xboole_0(B_72,C_73)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_467,plain,(
    ! [A_21,C_73] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_73)) = k5_xboole_0(k1_xboole_0,C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_390])).

tff(c_530,plain,(
    ! [A_76,C_77] : k5_xboole_0(A_76,k5_xboole_0(A_76,C_77)) = C_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_467])).

tff(c_582,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_530])).

tff(c_26,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_480,plain,(
    ! [A_21,C_73] : k5_xboole_0(A_21,k5_xboole_0(A_21,C_73)) = C_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_467])).

tff(c_635,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k5_xboole_0(B_80,A_79)) = B_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_530])).

tff(c_671,plain,(
    ! [A_21,C_73] : k5_xboole_0(k5_xboole_0(A_21,C_73),C_73) = A_21 ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_635])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_58,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_215,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [C_28,A_24] :
      ( r1_tarski(C_28,A_24)
      | ~ r2_hidden(C_28,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_222,plain,(
    ! [B_65,A_24] :
      ( r1_tarski(B_65,A_24)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_24))
      | v1_xboole_0(k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_215,c_36])).

tff(c_1086,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_222])).

tff(c_1099,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1086])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( k2_xboole_0(A_13,B_14) = B_14
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1103,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1099,c_24])).

tff(c_34,plain,(
    ! [A_22,B_23] : k5_xboole_0(k5_xboole_0(A_22,B_23),k2_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1109,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_3') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_34])).

tff(c_1112,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_1109])).

tff(c_22,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1117,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_22])).

tff(c_1120,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1117])).

tff(c_28,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1125,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1120,c_28])).

tff(c_1128,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1125])).

tff(c_1178,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1128,c_34])).

tff(c_1181,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_2,c_2,c_1178])).

tff(c_720,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_733,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_720])).

tff(c_1130,plain,(
    ! [A_93,C_94,B_95] :
      ( r2_hidden(A_93,C_94)
      | ~ r2_hidden(A_93,B_95)
      | r2_hidden(A_93,k5_xboole_0(B_95,C_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_23820,plain,(
    ! [A_247,A_248,B_249] :
      ( r2_hidden(A_247,k3_xboole_0(A_248,B_249))
      | ~ r2_hidden(A_247,A_248)
      | r2_hidden(A_247,k4_xboole_0(A_248,B_249)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1130])).

tff(c_23838,plain,(
    ! [A_247] :
      ( r2_hidden(A_247,k3_xboole_0('#skF_3','#skF_4'))
      | ~ r2_hidden(A_247,'#skF_3')
      | r2_hidden(A_247,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_733,c_23820])).

tff(c_24244,plain,(
    ! [A_252] :
      ( r2_hidden(A_252,'#skF_4')
      | ~ r2_hidden(A_252,'#skF_3')
      | r2_hidden(A_252,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_23838])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24253,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_24244,c_60])).

tff(c_24260,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_24253])).

tff(c_24263,plain,
    ( ~ m1_subset_1('#skF_5','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_24260])).

tff(c_24266,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24263])).

tff(c_24268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_24266])).

tff(c_24270,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24277,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24270,c_8])).

tff(c_24281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_24277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.74/5.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.94  
% 11.74/5.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.94  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.74/5.94  
% 11.74/5.94  %Foreground sorts:
% 11.74/5.94  
% 11.74/5.94  
% 11.74/5.94  %Background operators:
% 11.74/5.94  
% 11.74/5.94  
% 11.74/5.94  %Foreground operators:
% 11.74/5.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.74/5.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.74/5.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.74/5.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.74/5.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.74/5.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.74/5.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.74/5.94  tff('#skF_5', type, '#skF_5': $i).
% 11.74/5.94  tff('#skF_3', type, '#skF_3': $i).
% 11.74/5.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.74/5.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.74/5.94  tff('#skF_4', type, '#skF_4': $i).
% 11.74/5.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.74/5.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.74/5.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.74/5.94  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.74/5.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.74/5.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.74/5.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.74/5.94  
% 11.74/5.96  tff(f_100, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 11.74/5.96  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.74/5.96  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.74/5.96  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 11.74/5.96  tff(f_56, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 11.74/5.96  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 11.74/5.96  tff(f_58, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.74/5.96  tff(f_54, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 11.74/5.96  tff(f_50, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 11.74/5.96  tff(f_85, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.74/5.96  tff(f_65, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.74/5.96  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.74/5.96  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.74/5.96  tff(f_52, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 11.74/5.96  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.74/5.96  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 11.74/5.96  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 11.74/5.96  tff(c_68, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.74/5.96  tff(c_64, plain, (m1_subset_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.74/5.96  tff(c_156, plain, (![B_54, A_55]: (v1_xboole_0(B_54) | ~m1_subset_1(B_54, A_55) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.74/5.96  tff(c_168, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_64, c_156])).
% 11.74/5.96  tff(c_169, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_168])).
% 11.74/5.96  tff(c_50, plain, (![B_30, A_29]: (r2_hidden(B_30, A_29) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.74/5.96  tff(c_62, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.74/5.96  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.74/5.96  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.74/5.96  tff(c_32, plain, (![A_21]: (k5_xboole_0(A_21, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.74/5.96  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.74/5.96  tff(c_235, plain, (![A_67, B_68]: (k5_xboole_0(k5_xboole_0(A_67, B_68), k2_xboole_0(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.74/5.96  tff(c_277, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_235])).
% 11.74/5.96  tff(c_283, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32, c_277])).
% 11.74/5.96  tff(c_390, plain, (![A_71, B_72, C_73]: (k5_xboole_0(k5_xboole_0(A_71, B_72), C_73)=k5_xboole_0(A_71, k5_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.74/5.96  tff(c_467, plain, (![A_21, C_73]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_73))=k5_xboole_0(k1_xboole_0, C_73))), inference(superposition, [status(thm), theory('equality')], [c_32, c_390])).
% 11.74/5.96  tff(c_530, plain, (![A_76, C_77]: (k5_xboole_0(A_76, k5_xboole_0(A_76, C_77))=C_77)), inference(demodulation, [status(thm), theory('equality')], [c_283, c_467])).
% 11.74/5.96  tff(c_582, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_530])).
% 11.74/5.96  tff(c_26, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.74/5.96  tff(c_480, plain, (![A_21, C_73]: (k5_xboole_0(A_21, k5_xboole_0(A_21, C_73))=C_73)), inference(demodulation, [status(thm), theory('equality')], [c_283, c_467])).
% 11.74/5.96  tff(c_635, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k5_xboole_0(B_80, A_79))=B_80)), inference(superposition, [status(thm), theory('equality')], [c_2, c_530])).
% 11.74/5.96  tff(c_671, plain, (![A_21, C_73]: (k5_xboole_0(k5_xboole_0(A_21, C_73), C_73)=A_21)), inference(superposition, [status(thm), theory('equality')], [c_480, c_635])).
% 11.74/5.96  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.74/5.96  tff(c_58, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 11.74/5.96  tff(c_215, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | ~m1_subset_1(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.74/5.96  tff(c_36, plain, (![C_28, A_24]: (r1_tarski(C_28, A_24) | ~r2_hidden(C_28, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.74/5.96  tff(c_222, plain, (![B_65, A_24]: (r1_tarski(B_65, A_24) | ~m1_subset_1(B_65, k1_zfmisc_1(A_24)) | v1_xboole_0(k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_215, c_36])).
% 11.74/5.96  tff(c_1086, plain, (![B_91, A_92]: (r1_tarski(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)))), inference(negUnitSimplification, [status(thm)], [c_58, c_222])).
% 11.74/5.96  tff(c_1099, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_1086])).
% 11.74/5.96  tff(c_24, plain, (![A_13, B_14]: (k2_xboole_0(A_13, B_14)=B_14 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.74/5.96  tff(c_1103, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1099, c_24])).
% 11.74/5.96  tff(c_34, plain, (![A_22, B_23]: (k5_xboole_0(k5_xboole_0(A_22, B_23), k2_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.74/5.96  tff(c_1109, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_3')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1103, c_34])).
% 11.74/5.96  tff(c_1112, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_671, c_1109])).
% 11.74/5.96  tff(c_22, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.74/5.96  tff(c_1117, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_22])).
% 11.74/5.96  tff(c_1120, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1117])).
% 11.74/5.96  tff(c_28, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.74/5.96  tff(c_1125, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1120, c_28])).
% 11.74/5.96  tff(c_1128, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1125])).
% 11.74/5.96  tff(c_1178, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1128, c_34])).
% 11.74/5.96  tff(c_1181, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_582, c_2, c_2, c_1178])).
% 11.74/5.96  tff(c_720, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.74/5.96  tff(c_733, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_720])).
% 11.74/5.96  tff(c_1130, plain, (![A_93, C_94, B_95]: (r2_hidden(A_93, C_94) | ~r2_hidden(A_93, B_95) | r2_hidden(A_93, k5_xboole_0(B_95, C_94)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 11.74/5.96  tff(c_23820, plain, (![A_247, A_248, B_249]: (r2_hidden(A_247, k3_xboole_0(A_248, B_249)) | ~r2_hidden(A_247, A_248) | r2_hidden(A_247, k4_xboole_0(A_248, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1130])).
% 11.74/5.96  tff(c_23838, plain, (![A_247]: (r2_hidden(A_247, k3_xboole_0('#skF_3', '#skF_4')) | ~r2_hidden(A_247, '#skF_3') | r2_hidden(A_247, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_733, c_23820])).
% 11.74/5.96  tff(c_24244, plain, (![A_252]: (r2_hidden(A_252, '#skF_4') | ~r2_hidden(A_252, '#skF_3') | r2_hidden(A_252, k3_subset_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_23838])).
% 11.74/5.96  tff(c_60, plain, (~r2_hidden('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.74/5.96  tff(c_24253, plain, (r2_hidden('#skF_5', '#skF_4') | ~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_24244, c_60])).
% 11.74/5.96  tff(c_24260, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_24253])).
% 11.74/5.96  tff(c_24263, plain, (~m1_subset_1('#skF_5', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_24260])).
% 11.74/5.96  tff(c_24266, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24263])).
% 11.74/5.96  tff(c_24268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_24266])).
% 11.74/5.96  tff(c_24270, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_168])).
% 11.74/5.96  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.74/5.96  tff(c_24277, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_24270, c_8])).
% 11.74/5.96  tff(c_24281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_24277])).
% 11.74/5.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.74/5.96  
% 11.74/5.96  Inference rules
% 11.74/5.96  ----------------------
% 11.74/5.96  #Ref     : 0
% 11.74/5.96  #Sup     : 6497
% 11.74/5.96  #Fact    : 0
% 11.74/5.96  #Define  : 0
% 11.74/5.96  #Split   : 6
% 11.74/5.96  #Chain   : 0
% 11.74/5.96  #Close   : 0
% 11.74/5.96  
% 11.74/5.96  Ordering : KBO
% 11.74/5.96  
% 11.74/5.96  Simplification rules
% 11.74/5.96  ----------------------
% 11.74/5.96  #Subsume      : 424
% 11.74/5.96  #Demod        : 7358
% 11.74/5.96  #Tautology    : 2372
% 11.74/5.96  #SimpNegUnit  : 7
% 11.74/5.96  #BackRed      : 5
% 11.74/5.96  
% 11.74/5.96  #Partial instantiations: 0
% 11.74/5.96  #Strategies tried      : 1
% 11.74/5.96  
% 11.74/5.96  Timing (in seconds)
% 11.74/5.96  ----------------------
% 11.74/5.96  Preprocessing        : 0.46
% 11.74/5.96  Parsing              : 0.26
% 11.74/5.96  CNF conversion       : 0.03
% 11.74/5.96  Main loop            : 4.78
% 11.74/5.96  Inferencing          : 0.75
% 11.74/5.96  Reduction            : 3.24
% 11.74/5.96  Demodulation         : 3.03
% 11.74/5.96  BG Simplification    : 0.13
% 11.74/5.96  Subsumption          : 0.51
% 11.74/5.96  Abstraction          : 0.16
% 11.74/5.96  MUC search           : 0.00
% 11.74/5.96  Cooper               : 0.00
% 11.74/5.96  Total                : 5.27
% 11.74/5.96  Index Insertion      : 0.00
% 11.74/5.96  Index Deletion       : 0.00
% 11.74/5.96  Index Matching       : 0.00
% 11.74/5.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
