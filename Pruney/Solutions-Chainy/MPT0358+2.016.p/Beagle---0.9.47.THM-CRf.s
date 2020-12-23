%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:02 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.43s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 171 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 293 expanded)
%              Number of equality atoms :   37 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_78,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_85,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_284,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2825,plain,(
    ! [A_199,B_200,B_201] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_199,B_200),B_201),A_199)
      | r1_tarski(k4_xboole_0(A_199,B_200),B_201) ) ),
    inference(resolution,[status(thm)],[c_284,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2915,plain,(
    ! [A_202,B_203] : r1_tarski(k4_xboole_0(A_202,B_203),A_202) ),
    inference(resolution,[status(thm)],[c_2825,c_6])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3065,plain,(
    ! [A_209,B_210] : k2_xboole_0(k4_xboole_0(A_209,B_210),A_209) = A_209 ),
    inference(resolution,[status(thm)],[c_2915,c_30])).

tff(c_56,plain,(
    ! [A_28] : k1_subset_1(A_28) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_64,plain,
    ( k1_subset_1('#skF_6') != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,
    ( k1_xboole_0 != '#skF_7'
    | ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_70,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_subset_1('#skF_6') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_71,plain,
    ( r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_70])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_71])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_18] : k2_xboole_0(A_18,'#skF_7') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_32])).

tff(c_3072,plain,(
    ! [B_210] : k4_xboole_0('#skF_7',B_210) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_3065,c_138])).

tff(c_301,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_284,c_6])).

tff(c_60,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_38,plain,(
    ! [C_25,A_21] :
      ( r2_hidden(C_25,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_183,plain,(
    ! [C_25,A_21] :
      ( m1_subset_1(C_25,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_186,plain,(
    ! [C_25,A_21] :
      ( m1_subset_1(C_25,k1_zfmisc_1(A_21))
      | ~ r1_tarski(C_25,A_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_183])).

tff(c_442,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_551,plain,(
    ! [A_90,C_91] :
      ( k4_xboole_0(A_90,C_91) = k3_subset_1(A_90,C_91)
      | ~ r1_tarski(C_91,A_90) ) ),
    inference(resolution,[status(thm)],[c_186,c_442])).

tff(c_558,plain,(
    ! [A_66] : k4_xboole_0(A_66,A_66) = k3_subset_1(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_301,c_551])).

tff(c_304,plain,(
    ! [A_68] : r1_tarski(A_68,A_68) ),
    inference(resolution,[status(thm)],[c_284,c_6])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_343,plain,(
    ! [A_73] : k3_xboole_0(A_73,A_73) = A_73 ),
    inference(resolution,[status(thm)],[c_304,c_34])).

tff(c_28,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_349,plain,(
    ! [A_73] : k5_xboole_0(A_73,A_73) = k4_xboole_0(A_73,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_28])).

tff(c_575,plain,(
    ! [A_73] : k5_xboole_0(A_73,A_73) = k3_subset_1(A_73,A_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_349])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_192,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_199,plain,(
    ! [B_57,A_21] :
      ( r1_tarski(B_57,A_21)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_192,c_36])).

tff(c_204,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_199])).

tff(c_217,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_204])).

tff(c_225,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_217,c_34])).

tff(c_233,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_28])).

tff(c_594,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k3_subset_1('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_233])).

tff(c_3097,plain,(
    k3_subset_1('#skF_7','#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3072,c_594])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_332,plain,(
    ! [D_70,B_71,A_72] :
      ( ~ r2_hidden(D_70,B_71)
      | ~ r2_hidden(D_70,k4_xboole_0(A_72,B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_341,plain,(
    ! [A_72,B_71,B_4] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_72,B_71),B_4),B_71)
      | r1_tarski(k4_xboole_0(A_72,B_71),B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_2829,plain,(
    ! [A_199,B_201] : r1_tarski(k4_xboole_0(A_199,A_199),B_201) ),
    inference(resolution,[status(thm)],[c_2825,c_341])).

tff(c_2896,plain,(
    ! [A_199,B_201] : r1_tarski(k3_subset_1(A_199,A_199),B_201) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_2829])).

tff(c_3178,plain,(
    ! [B_201] : r1_tarski('#skF_7',B_201) ),
    inference(superposition,[status(thm),theory(equality)],[c_3097,c_2896])).

tff(c_3192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3178,c_135])).

tff(c_3193,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3194,plain,(
    r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3483,plain,(
    ! [C_245,B_246,A_247] :
      ( r2_hidden(C_245,B_246)
      | ~ r2_hidden(C_245,A_247)
      | ~ r1_tarski(A_247,B_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4011,plain,(
    ! [A_288,B_289,B_290] :
      ( r2_hidden('#skF_1'(A_288,B_289),B_290)
      | ~ r1_tarski(A_288,B_290)
      | r1_tarski(A_288,B_289) ) ),
    inference(resolution,[status(thm)],[c_8,c_3483])).

tff(c_3520,plain,(
    ! [A_249,B_250] :
      ( k4_xboole_0(A_249,B_250) = k3_subset_1(A_249,B_250)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(A_249)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3533,plain,(
    k4_xboole_0('#skF_6','#skF_7') = k3_subset_1('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_3520])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3538,plain,(
    ! [D_13] :
      ( ~ r2_hidden(D_13,'#skF_7')
      | ~ r2_hidden(D_13,k3_subset_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3533,c_12])).

tff(c_4625,plain,(
    ! [A_313,B_314] :
      ( ~ r2_hidden('#skF_1'(A_313,B_314),'#skF_7')
      | ~ r1_tarski(A_313,k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski(A_313,B_314) ) ),
    inference(resolution,[status(thm)],[c_4011,c_3538])).

tff(c_4636,plain,(
    ! [B_4] :
      ( ~ r1_tarski('#skF_7',k3_subset_1('#skF_6','#skF_7'))
      | r1_tarski('#skF_7',B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_4625])).

tff(c_4650,plain,(
    ! [B_315] : r1_tarski('#skF_7',B_315) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3194,c_4636])).

tff(c_4675,plain,(
    ! [B_316] : k2_xboole_0('#skF_7',B_316) = B_316 ),
    inference(resolution,[status(thm)],[c_4650,c_30])).

tff(c_4686,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_4675,c_32])).

tff(c_4701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3193,c_4686])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/1.97  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.98  
% 5.18/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.18/1.98  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.18/1.98  
% 5.18/1.98  %Foreground sorts:
% 5.18/1.98  
% 5.18/1.98  
% 5.18/1.98  %Background operators:
% 5.18/1.98  
% 5.18/1.98  
% 5.18/1.98  %Foreground operators:
% 5.18/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.18/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.18/1.98  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.18/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.18/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.18/1.98  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.18/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.18/1.98  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.18/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.18/1.98  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.18/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.18/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.18/1.98  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.18/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.18/1.98  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.18/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.18/1.98  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.18/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.18/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.18/1.98  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.18/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.18/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.18/1.98  
% 5.43/2.00  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.43/2.00  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.43/2.00  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.43/2.00  tff(f_78, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.43/2.00  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 5.43/2.00  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.43/2.00  tff(f_85, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.43/2.00  tff(f_63, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.43/2.00  tff(f_76, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.43/2.00  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.43/2.00  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.43/2.00  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.43/2.00  tff(c_284, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.43/2.00  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.00  tff(c_2825, plain, (![A_199, B_200, B_201]: (r2_hidden('#skF_1'(k4_xboole_0(A_199, B_200), B_201), A_199) | r1_tarski(k4_xboole_0(A_199, B_200), B_201))), inference(resolution, [status(thm)], [c_284, c_14])).
% 5.43/2.00  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.43/2.00  tff(c_2915, plain, (![A_202, B_203]: (r1_tarski(k4_xboole_0(A_202, B_203), A_202))), inference(resolution, [status(thm)], [c_2825, c_6])).
% 5.43/2.00  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.43/2.00  tff(c_3065, plain, (![A_209, B_210]: (k2_xboole_0(k4_xboole_0(A_209, B_210), A_209)=A_209)), inference(resolution, [status(thm)], [c_2915, c_30])).
% 5.43/2.00  tff(c_56, plain, (![A_28]: (k1_subset_1(A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.43/2.00  tff(c_64, plain, (k1_subset_1('#skF_6')!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.43/2.00  tff(c_72, plain, (k1_xboole_0!='#skF_7' | ~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_64])).
% 5.43/2.00  tff(c_135, plain, (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_72])).
% 5.43/2.00  tff(c_70, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_subset_1('#skF_6')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.43/2.00  tff(c_71, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_70])).
% 5.43/2.00  tff(c_137, plain, (k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_135, c_71])).
% 5.43/2.00  tff(c_32, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.43/2.00  tff(c_138, plain, (![A_18]: (k2_xboole_0(A_18, '#skF_7')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_32])).
% 5.43/2.00  tff(c_3072, plain, (![B_210]: (k4_xboole_0('#skF_7', B_210)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3065, c_138])).
% 5.43/2.00  tff(c_301, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_284, c_6])).
% 5.43/2.00  tff(c_60, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.43/2.00  tff(c_38, plain, (![C_25, A_21]: (r2_hidden(C_25, k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.43/2.00  tff(c_180, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/2.00  tff(c_183, plain, (![C_25, A_21]: (m1_subset_1(C_25, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(resolution, [status(thm)], [c_38, c_180])).
% 5.43/2.00  tff(c_186, plain, (![C_25, A_21]: (m1_subset_1(C_25, k1_zfmisc_1(A_21)) | ~r1_tarski(C_25, A_21))), inference(negUnitSimplification, [status(thm)], [c_60, c_183])).
% 5.43/2.00  tff(c_442, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.43/2.00  tff(c_551, plain, (![A_90, C_91]: (k4_xboole_0(A_90, C_91)=k3_subset_1(A_90, C_91) | ~r1_tarski(C_91, A_90))), inference(resolution, [status(thm)], [c_186, c_442])).
% 5.43/2.00  tff(c_558, plain, (![A_66]: (k4_xboole_0(A_66, A_66)=k3_subset_1(A_66, A_66))), inference(resolution, [status(thm)], [c_301, c_551])).
% 5.43/2.00  tff(c_304, plain, (![A_68]: (r1_tarski(A_68, A_68))), inference(resolution, [status(thm)], [c_284, c_6])).
% 5.43/2.00  tff(c_34, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.43/2.00  tff(c_343, plain, (![A_73]: (k3_xboole_0(A_73, A_73)=A_73)), inference(resolution, [status(thm)], [c_304, c_34])).
% 5.43/2.00  tff(c_28, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.43/2.00  tff(c_349, plain, (![A_73]: (k5_xboole_0(A_73, A_73)=k4_xboole_0(A_73, A_73))), inference(superposition, [status(thm), theory('equality')], [c_343, c_28])).
% 5.43/2.00  tff(c_575, plain, (![A_73]: (k5_xboole_0(A_73, A_73)=k3_subset_1(A_73, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_349])).
% 5.43/2.00  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.43/2.00  tff(c_192, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.43/2.00  tff(c_36, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.43/2.00  tff(c_199, plain, (![B_57, A_21]: (r1_tarski(B_57, A_21) | ~m1_subset_1(B_57, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_192, c_36])).
% 5.43/2.00  tff(c_204, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_60, c_199])).
% 5.43/2.00  tff(c_217, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_204])).
% 5.43/2.00  tff(c_225, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_217, c_34])).
% 5.43/2.00  tff(c_233, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_225, c_28])).
% 5.43/2.00  tff(c_594, plain, (k4_xboole_0('#skF_7', '#skF_6')=k3_subset_1('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_575, c_233])).
% 5.43/2.00  tff(c_3097, plain, (k3_subset_1('#skF_7', '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3072, c_594])).
% 5.43/2.00  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.43/2.00  tff(c_332, plain, (![D_70, B_71, A_72]: (~r2_hidden(D_70, B_71) | ~r2_hidden(D_70, k4_xboole_0(A_72, B_71)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.00  tff(c_341, plain, (![A_72, B_71, B_4]: (~r2_hidden('#skF_1'(k4_xboole_0(A_72, B_71), B_4), B_71) | r1_tarski(k4_xboole_0(A_72, B_71), B_4))), inference(resolution, [status(thm)], [c_8, c_332])).
% 5.43/2.00  tff(c_2829, plain, (![A_199, B_201]: (r1_tarski(k4_xboole_0(A_199, A_199), B_201))), inference(resolution, [status(thm)], [c_2825, c_341])).
% 5.43/2.00  tff(c_2896, plain, (![A_199, B_201]: (r1_tarski(k3_subset_1(A_199, A_199), B_201))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_2829])).
% 5.43/2.00  tff(c_3178, plain, (![B_201]: (r1_tarski('#skF_7', B_201))), inference(superposition, [status(thm), theory('equality')], [c_3097, c_2896])).
% 5.43/2.00  tff(c_3192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3178, c_135])).
% 5.43/2.00  tff(c_3193, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_72])).
% 5.43/2.00  tff(c_3194, plain, (r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_72])).
% 5.43/2.00  tff(c_3483, plain, (![C_245, B_246, A_247]: (r2_hidden(C_245, B_246) | ~r2_hidden(C_245, A_247) | ~r1_tarski(A_247, B_246))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.43/2.00  tff(c_4011, plain, (![A_288, B_289, B_290]: (r2_hidden('#skF_1'(A_288, B_289), B_290) | ~r1_tarski(A_288, B_290) | r1_tarski(A_288, B_289))), inference(resolution, [status(thm)], [c_8, c_3483])).
% 5.43/2.00  tff(c_3520, plain, (![A_249, B_250]: (k4_xboole_0(A_249, B_250)=k3_subset_1(A_249, B_250) | ~m1_subset_1(B_250, k1_zfmisc_1(A_249)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.43/2.00  tff(c_3533, plain, (k4_xboole_0('#skF_6', '#skF_7')=k3_subset_1('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_3520])).
% 5.43/2.00  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.43/2.00  tff(c_3538, plain, (![D_13]: (~r2_hidden(D_13, '#skF_7') | ~r2_hidden(D_13, k3_subset_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_3533, c_12])).
% 5.43/2.00  tff(c_4625, plain, (![A_313, B_314]: (~r2_hidden('#skF_1'(A_313, B_314), '#skF_7') | ~r1_tarski(A_313, k3_subset_1('#skF_6', '#skF_7')) | r1_tarski(A_313, B_314))), inference(resolution, [status(thm)], [c_4011, c_3538])).
% 5.43/2.00  tff(c_4636, plain, (![B_4]: (~r1_tarski('#skF_7', k3_subset_1('#skF_6', '#skF_7')) | r1_tarski('#skF_7', B_4))), inference(resolution, [status(thm)], [c_8, c_4625])).
% 5.43/2.00  tff(c_4650, plain, (![B_315]: (r1_tarski('#skF_7', B_315))), inference(demodulation, [status(thm), theory('equality')], [c_3194, c_4636])).
% 5.43/2.00  tff(c_4675, plain, (![B_316]: (k2_xboole_0('#skF_7', B_316)=B_316)), inference(resolution, [status(thm)], [c_4650, c_30])).
% 5.43/2.00  tff(c_4686, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_4675, c_32])).
% 5.43/2.00  tff(c_4701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3193, c_4686])).
% 5.43/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.43/2.00  
% 5.43/2.00  Inference rules
% 5.43/2.00  ----------------------
% 5.43/2.00  #Ref     : 0
% 5.43/2.00  #Sup     : 1062
% 5.43/2.00  #Fact    : 0
% 5.43/2.00  #Define  : 0
% 5.43/2.00  #Split   : 19
% 5.43/2.00  #Chain   : 0
% 5.43/2.00  #Close   : 0
% 5.43/2.00  
% 5.43/2.00  Ordering : KBO
% 5.43/2.00  
% 5.43/2.00  Simplification rules
% 5.43/2.00  ----------------------
% 5.43/2.00  #Subsume      : 86
% 5.43/2.00  #Demod        : 251
% 5.43/2.00  #Tautology    : 383
% 5.43/2.00  #SimpNegUnit  : 65
% 5.43/2.00  #BackRed      : 28
% 5.43/2.00  
% 5.43/2.00  #Partial instantiations: 0
% 5.43/2.00  #Strategies tried      : 1
% 5.43/2.00  
% 5.43/2.00  Timing (in seconds)
% 5.43/2.00  ----------------------
% 5.43/2.00  Preprocessing        : 0.31
% 5.43/2.00  Parsing              : 0.16
% 5.43/2.00  CNF conversion       : 0.02
% 5.43/2.00  Main loop            : 0.93
% 5.43/2.00  Inferencing          : 0.31
% 5.43/2.00  Reduction            : 0.29
% 5.43/2.00  Demodulation         : 0.20
% 5.43/2.00  BG Simplification    : 0.04
% 5.43/2.00  Subsumption          : 0.20
% 5.43/2.00  Abstraction          : 0.04
% 5.43/2.00  MUC search           : 0.00
% 5.43/2.00  Cooper               : 0.00
% 5.43/2.00  Total                : 1.27
% 5.43/2.00  Index Insertion      : 0.00
% 5.43/2.00  Index Deletion       : 0.00
% 5.43/2.00  Index Matching       : 0.00
% 5.43/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
