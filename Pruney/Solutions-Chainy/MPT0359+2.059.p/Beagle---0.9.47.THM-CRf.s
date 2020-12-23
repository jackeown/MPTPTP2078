%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:17 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 217 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  114 ( 356 expanded)
%              Number of equality atoms :   38 ( 125 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_40,plain,(
    ! [A_22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_111,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [B_38,A_5] :
      ( r1_tarski(B_38,A_5)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_111,c_6])).

tff(c_119,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_115])).

tff(c_132,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_26,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_52,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38])).

tff(c_54,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_52])).

tff(c_255,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_266,plain,(
    ! [A_22] : k3_subset_1(A_22,k3_subset_1(A_22,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_255])).

tff(c_272,plain,(
    ! [A_22] : k3_subset_1(A_22,A_22) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_266])).

tff(c_44,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_51,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_83,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50])).

tff(c_84,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_53])).

tff(c_85,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83])).

tff(c_274,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_85])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_274])).

tff(c_278,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_323,plain,(
    ! [B_73,A_74] :
      ( r2_hidden(B_73,A_74)
      | ~ m1_subset_1(B_73,A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_330,plain,(
    ! [B_73,A_5] :
      ( r1_tarski(B_73,A_5)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_323,c_6])).

tff(c_335,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(B_75,A_76)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_330])).

tff(c_351,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_335])).

tff(c_352,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(resolution,[status(thm)],[c_40,c_335])).

tff(c_279,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_462,plain,(
    ! [A_88,B_89] :
      ( k3_subset_1(A_88,k3_subset_1(A_88,B_89)) = B_89
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_480,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_462])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_390,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k3_subset_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1006,plain,(
    ! [A_112,B_113] :
      ( k4_xboole_0(A_112,k3_subset_1(A_112,B_113)) = k3_subset_1(A_112,k3_subset_1(A_112,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_32,c_390])).

tff(c_1017,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_1006])).

tff(c_1026,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_1017])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1032,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1026,c_4])).

tff(c_1036,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_1032])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_302,plain,(
    ! [B_67,A_68] :
      ( m1_subset_1(B_67,A_68)
      | ~ r2_hidden(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_305,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_308,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_305])).

tff(c_667,plain,(
    ! [A_99,C_100] :
      ( k4_xboole_0(A_99,C_100) = k3_subset_1(A_99,C_100)
      | ~ r1_tarski(C_100,A_99) ) ),
    inference(resolution,[status(thm)],[c_308,c_390])).

tff(c_690,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_279,c_667])).

tff(c_694,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_4',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_4])).

tff(c_726,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_4',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_694])).

tff(c_1039,plain,(
    ~ r1_tarski(k1_xboole_0,k3_subset_1('#skF_4',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1036,c_726])).

tff(c_1047,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_54,c_1039])).

tff(c_1048,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_694])).

tff(c_478,plain,(
    ! [A_5,C_9] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,C_9)) = C_9
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_308,c_462])).

tff(c_1060,plain,
    ( k3_subset_1('#skF_3',k1_xboole_0) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_478])).

tff(c_1070,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_54,c_1060])).

tff(c_1072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_1070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.89/1.45  
% 2.89/1.45  %Foreground sorts:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Background operators:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Foreground operators:
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.89/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.89/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.89/1.45  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.89/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.89/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.89/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.45  
% 2.89/1.47  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.89/1.47  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.89/1.47  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.89/1.47  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.89/1.47  tff(f_53, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.89/1.47  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.89/1.47  tff(f_72, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.89/1.47  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.89/1.47  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.89/1.47  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.89/1.47  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.89/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.89/1.47  tff(c_40, plain, (![A_22]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.89/1.47  tff(c_34, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.89/1.47  tff(c_111, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.47  tff(c_6, plain, (![C_9, A_5]: (r1_tarski(C_9, A_5) | ~r2_hidden(C_9, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.47  tff(c_115, plain, (![B_38, A_5]: (r1_tarski(B_38, A_5) | ~m1_subset_1(B_38, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_111, c_6])).
% 2.89/1.47  tff(c_119, plain, (![B_40, A_41]: (r1_tarski(B_40, A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(negUnitSimplification, [status(thm)], [c_34, c_115])).
% 2.89/1.47  tff(c_132, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(resolution, [status(thm)], [c_40, c_119])).
% 2.89/1.47  tff(c_26, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.89/1.47  tff(c_28, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.89/1.47  tff(c_38, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.89/1.47  tff(c_52, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38])).
% 2.89/1.47  tff(c_54, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_52])).
% 2.89/1.47  tff(c_255, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.47  tff(c_266, plain, (![A_22]: (k3_subset_1(A_22, k3_subset_1(A_22, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_255])).
% 2.89/1.47  tff(c_272, plain, (![A_22]: (k3_subset_1(A_22, A_22)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_266])).
% 2.89/1.47  tff(c_44, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.47  tff(c_51, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44])).
% 2.89/1.47  tff(c_83, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_51])).
% 2.89/1.47  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.47  tff(c_53, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_50])).
% 2.89/1.47  tff(c_84, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_83, c_53])).
% 2.89/1.47  tff(c_85, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83])).
% 2.89/1.47  tff(c_274, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_85])).
% 2.89/1.47  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_274])).
% 2.89/1.47  tff(c_278, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_51])).
% 2.89/1.47  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.47  tff(c_323, plain, (![B_73, A_74]: (r2_hidden(B_73, A_74) | ~m1_subset_1(B_73, A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.47  tff(c_330, plain, (![B_73, A_5]: (r1_tarski(B_73, A_5) | ~m1_subset_1(B_73, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_323, c_6])).
% 2.89/1.47  tff(c_335, plain, (![B_75, A_76]: (r1_tarski(B_75, A_76) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)))), inference(negUnitSimplification, [status(thm)], [c_34, c_330])).
% 2.89/1.47  tff(c_351, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_335])).
% 2.89/1.47  tff(c_352, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(resolution, [status(thm)], [c_40, c_335])).
% 2.89/1.47  tff(c_279, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_51])).
% 2.89/1.47  tff(c_462, plain, (![A_88, B_89]: (k3_subset_1(A_88, k3_subset_1(A_88, B_89))=B_89 | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.89/1.47  tff(c_480, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_42, c_462])).
% 2.89/1.47  tff(c_32, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.89/1.47  tff(c_390, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k3_subset_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.89/1.47  tff(c_1006, plain, (![A_112, B_113]: (k4_xboole_0(A_112, k3_subset_1(A_112, B_113))=k3_subset_1(A_112, k3_subset_1(A_112, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(resolution, [status(thm)], [c_32, c_390])).
% 2.89/1.47  tff(c_1017, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_1006])).
% 2.89/1.47  tff(c_1026, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_1017])).
% 2.89/1.47  tff(c_4, plain, (![A_3, B_4]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k4_xboole_0(B_4, A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.47  tff(c_1032, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1026, c_4])).
% 2.89/1.47  tff(c_1036, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_279, c_1032])).
% 2.89/1.47  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.89/1.47  tff(c_302, plain, (![B_67, A_68]: (m1_subset_1(B_67, A_68) | ~r2_hidden(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.47  tff(c_305, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_8, c_302])).
% 2.89/1.47  tff(c_308, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(negUnitSimplification, [status(thm)], [c_34, c_305])).
% 2.89/1.47  tff(c_667, plain, (![A_99, C_100]: (k4_xboole_0(A_99, C_100)=k3_subset_1(A_99, C_100) | ~r1_tarski(C_100, A_99))), inference(resolution, [status(thm)], [c_308, c_390])).
% 2.89/1.47  tff(c_690, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_279, c_667])).
% 2.89/1.47  tff(c_694, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_4', k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_690, c_4])).
% 2.89/1.47  tff(c_726, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_4', k3_subset_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_694])).
% 2.89/1.47  tff(c_1039, plain, (~r1_tarski(k1_xboole_0, k3_subset_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1036, c_726])).
% 2.89/1.47  tff(c_1047, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_54, c_1039])).
% 2.89/1.47  tff(c_1048, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_694])).
% 2.89/1.47  tff(c_478, plain, (![A_5, C_9]: (k3_subset_1(A_5, k3_subset_1(A_5, C_9))=C_9 | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_308, c_462])).
% 2.89/1.47  tff(c_1060, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1048, c_478])).
% 2.89/1.47  tff(c_1070, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_54, c_1060])).
% 2.89/1.47  tff(c_1072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_1070])).
% 2.89/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.47  
% 2.89/1.47  Inference rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Ref     : 0
% 2.89/1.47  #Sup     : 221
% 2.89/1.47  #Fact    : 0
% 2.89/1.47  #Define  : 0
% 2.89/1.47  #Split   : 3
% 2.89/1.47  #Chain   : 0
% 2.89/1.47  #Close   : 0
% 2.89/1.47  
% 2.89/1.47  Ordering : KBO
% 2.89/1.47  
% 2.89/1.47  Simplification rules
% 2.89/1.47  ----------------------
% 2.89/1.47  #Subsume      : 44
% 2.89/1.47  #Demod        : 130
% 2.89/1.47  #Tautology    : 127
% 2.89/1.47  #SimpNegUnit  : 7
% 2.89/1.47  #BackRed      : 17
% 2.89/1.47  
% 2.89/1.47  #Partial instantiations: 0
% 2.89/1.47  #Strategies tried      : 1
% 2.89/1.47  
% 2.89/1.47  Timing (in seconds)
% 2.89/1.47  ----------------------
% 3.04/1.47  Preprocessing        : 0.32
% 3.04/1.47  Parsing              : 0.16
% 3.04/1.47  CNF conversion       : 0.02
% 3.04/1.47  Main loop            : 0.37
% 3.04/1.47  Inferencing          : 0.14
% 3.04/1.47  Reduction            : 0.12
% 3.04/1.47  Demodulation         : 0.08
% 3.04/1.47  BG Simplification    : 0.02
% 3.04/1.47  Subsumption          : 0.06
% 3.04/1.47  Abstraction          : 0.02
% 3.04/1.47  MUC search           : 0.00
% 3.04/1.47  Cooper               : 0.00
% 3.04/1.47  Total                : 0.73
% 3.04/1.47  Index Insertion      : 0.00
% 3.04/1.47  Index Deletion       : 0.00
% 3.04/1.47  Index Matching       : 0.00
% 3.04/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
