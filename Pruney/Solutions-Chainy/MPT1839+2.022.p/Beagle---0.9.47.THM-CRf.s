%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 212 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  116 ( 403 expanded)
%              Number of equality atoms :   60 ( 157 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_16,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    ! [A_8,B_9] : k4_xboole_0(k3_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_419,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(A_72,B_71)
      | ~ v1_zfmisc_1(B_71)
      | v1_xboole_0(B_71)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4324,plain,(
    ! [B_200,A_201] :
      ( B_200 = A_201
      | ~ v1_zfmisc_1(B_200)
      | v1_xboole_0(B_200)
      | v1_xboole_0(A_201)
      | k4_xboole_0(A_201,B_200) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_419])).

tff(c_4326,plain,(
    ! [A_201] :
      ( A_201 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_201)
      | k4_xboole_0(A_201,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_4324])).

tff(c_4330,plain,(
    ! [A_202] :
      ( A_202 = '#skF_1'
      | v1_xboole_0(A_202)
      | k4_xboole_0(A_202,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_4326])).

tff(c_36,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4338,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4330,c_36])).

tff(c_4346,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_4338])).

tff(c_18,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_597,plain,(
    ! [A_79,A_80,B_81] :
      ( r1_tarski(A_79,A_80)
      | ~ r1_tarski(A_79,k4_xboole_0(A_80,B_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_14])).

tff(c_646,plain,(
    ! [A_80,B_81] : r1_tarski(k4_xboole_0(A_80,B_81),A_80) ),
    inference(resolution,[status(thm)],[c_8,c_597])).

tff(c_118,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1013,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | k4_xboole_0(A_100,B_99) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_118])).

tff(c_1028,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = A_80
      | k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_646,c_1013])).

tff(c_1180,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = A_107
      | k3_xboole_0(A_107,B_108) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1028])).

tff(c_95,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_34])).

tff(c_1239,plain,
    ( k1_xboole_0 != '#skF_1'
    | k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_103])).

tff(c_1284,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_4351,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4346,c_1284])).

tff(c_44,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | B_32 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_47,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_44])).

tff(c_4412,plain,(
    ! [A_203] :
      ( k1_xboole_0 = A_203
      | A_203 = '#skF_1'
      | k4_xboole_0(A_203,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4330,c_47])).

tff(c_4617,plain,(
    ! [B_206] :
      ( k3_xboole_0('#skF_1',B_206) = k1_xboole_0
      | k3_xboole_0('#skF_1',B_206) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4412])).

tff(c_62,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_54])).

tff(c_221,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_253,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_221])).

tff(c_152,plain,(
    ! [B_55] : k2_xboole_0(k3_xboole_0(B_55,B_55),k1_xboole_0) = B_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_134])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ r1_tarski(A_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_14])).

tff(c_571,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | k4_xboole_0(A_77,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_589,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_571,c_34])).

tff(c_596,plain,(
    k3_xboole_0('#skF_1','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_589])).

tff(c_4750,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_4617,c_596])).

tff(c_648,plain,(
    ! [A_82,B_83] : r1_tarski(k4_xboole_0(A_82,B_83),A_82) ),
    inference(resolution,[status(thm)],[c_8,c_597])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_693,plain,(
    ! [A_82,B_83] : k4_xboole_0(k4_xboole_0(A_82,B_83),A_82) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_648,c_12])).

tff(c_5183,plain,(
    ! [B_214] :
      ( k4_xboole_0('#skF_1',B_214) = k1_xboole_0
      | k4_xboole_0('#skF_1',B_214) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_693,c_4412])).

tff(c_5376,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5183,c_103])).

tff(c_237,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_221])).

tff(c_4374,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4346,c_237])).

tff(c_4403,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4374])).

tff(c_5392,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5376,c_4403])).

tff(c_5395,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4750,c_5392])).

tff(c_5397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4351,c_5395])).

tff(c_5399,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_5507,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5399,c_36])).

tff(c_5510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_5507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.84  
% 4.61/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.84  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.68/1.84  
% 4.68/1.84  %Foreground sorts:
% 4.68/1.84  
% 4.68/1.84  
% 4.68/1.84  %Background operators:
% 4.68/1.84  
% 4.68/1.84  
% 4.68/1.84  %Foreground operators:
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.68/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.68/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.84  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.68/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.68/1.84  
% 4.68/1.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.68/1.86  tff(f_42, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.68/1.86  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.68/1.86  tff(f_87, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 4.68/1.86  tff(f_75, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.68/1.86  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.68/1.86  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.86  tff(f_46, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.68/1.86  tff(f_40, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.68/1.86  tff(f_54, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 4.68/1.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.68/1.86  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.86  tff(c_54, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.86  tff(c_61, plain, (![A_8, B_9]: (k4_xboole_0(k3_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_54])).
% 4.68/1.86  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.86  tff(c_38, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.86  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.86  tff(c_419, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(A_72, B_71) | ~v1_zfmisc_1(B_71) | v1_xboole_0(B_71) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.86  tff(c_4324, plain, (![B_200, A_201]: (B_200=A_201 | ~v1_zfmisc_1(B_200) | v1_xboole_0(B_200) | v1_xboole_0(A_201) | k4_xboole_0(A_201, B_200)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_419])).
% 4.68/1.86  tff(c_4326, plain, (![A_201]: (A_201='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_201) | k4_xboole_0(A_201, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_4324])).
% 4.68/1.86  tff(c_4330, plain, (![A_202]: (A_202='#skF_1' | v1_xboole_0(A_202) | k4_xboole_0(A_202, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40, c_4326])).
% 4.68/1.86  tff(c_36, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.86  tff(c_4338, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4330, c_36])).
% 4.68/1.86  tff(c_4346, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_4338])).
% 4.68/1.86  tff(c_18, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.68/1.86  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.86  tff(c_134, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.68/1.86  tff(c_14, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.68/1.86  tff(c_597, plain, (![A_79, A_80, B_81]: (r1_tarski(A_79, A_80) | ~r1_tarski(A_79, k4_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_134, c_14])).
% 4.68/1.86  tff(c_646, plain, (![A_80, B_81]: (r1_tarski(k4_xboole_0(A_80, B_81), A_80))), inference(resolution, [status(thm)], [c_8, c_597])).
% 4.68/1.86  tff(c_118, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.68/1.86  tff(c_1013, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | k4_xboole_0(A_100, B_99)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_118])).
% 4.68/1.86  tff(c_1028, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=A_80 | k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_646, c_1013])).
% 4.68/1.86  tff(c_1180, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=A_107 | k3_xboole_0(A_107, B_108)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1028])).
% 4.68/1.86  tff(c_95, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.86  tff(c_34, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.86  tff(c_103, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_95, c_34])).
% 4.68/1.86  tff(c_1239, plain, (k1_xboole_0!='#skF_1' | k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1180, c_103])).
% 4.68/1.86  tff(c_1284, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1239])).
% 4.68/1.86  tff(c_4351, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4346, c_1284])).
% 4.68/1.86  tff(c_44, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | B_32=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.68/1.86  tff(c_47, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_2, c_44])).
% 4.68/1.86  tff(c_4412, plain, (![A_203]: (k1_xboole_0=A_203 | A_203='#skF_1' | k4_xboole_0(A_203, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4330, c_47])).
% 4.68/1.86  tff(c_4617, plain, (![B_206]: (k3_xboole_0('#skF_1', B_206)=k1_xboole_0 | k3_xboole_0('#skF_1', B_206)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_61, c_4412])).
% 4.68/1.86  tff(c_62, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_54])).
% 4.68/1.86  tff(c_221, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.68/1.86  tff(c_253, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_62, c_221])).
% 4.68/1.86  tff(c_152, plain, (![B_55]: (k2_xboole_0(k3_xboole_0(B_55, B_55), k1_xboole_0)=B_55)), inference(superposition, [status(thm), theory('equality')], [c_62, c_134])).
% 4.68/1.86  tff(c_164, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~r1_tarski(A_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_14])).
% 4.68/1.86  tff(c_571, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | k4_xboole_0(A_77, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_164])).
% 4.68/1.86  tff(c_589, plain, (k4_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_571, c_34])).
% 4.68/1.86  tff(c_596, plain, (k3_xboole_0('#skF_1', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_253, c_589])).
% 4.68/1.86  tff(c_4750, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_4617, c_596])).
% 4.68/1.86  tff(c_648, plain, (![A_82, B_83]: (r1_tarski(k4_xboole_0(A_82, B_83), A_82))), inference(resolution, [status(thm)], [c_8, c_597])).
% 4.68/1.86  tff(c_12, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.68/1.86  tff(c_693, plain, (![A_82, B_83]: (k4_xboole_0(k4_xboole_0(A_82, B_83), A_82)=k1_xboole_0)), inference(resolution, [status(thm)], [c_648, c_12])).
% 4.68/1.86  tff(c_5183, plain, (![B_214]: (k4_xboole_0('#skF_1', B_214)=k1_xboole_0 | k4_xboole_0('#skF_1', B_214)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_693, c_4412])).
% 4.68/1.86  tff(c_5376, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5183, c_103])).
% 4.68/1.86  tff(c_237, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k3_xboole_0(A_10, k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_221])).
% 4.68/1.86  tff(c_4374, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4346, c_237])).
% 4.68/1.86  tff(c_4403, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4374])).
% 4.68/1.86  tff(c_5392, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5376, c_4403])).
% 4.68/1.86  tff(c_5395, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4750, c_5392])).
% 4.68/1.86  tff(c_5397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4351, c_5395])).
% 4.68/1.86  tff(c_5399, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1239])).
% 4.68/1.86  tff(c_5507, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_5399, c_36])).
% 4.68/1.86  tff(c_5510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_5507])).
% 4.68/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.86  
% 4.68/1.86  Inference rules
% 4.68/1.86  ----------------------
% 4.68/1.86  #Ref     : 0
% 4.68/1.86  #Sup     : 1273
% 4.68/1.86  #Fact    : 2
% 4.68/1.86  #Define  : 0
% 4.68/1.86  #Split   : 1
% 4.68/1.86  #Chain   : 0
% 4.68/1.86  #Close   : 0
% 4.68/1.86  
% 4.68/1.86  Ordering : KBO
% 4.68/1.86  
% 4.68/1.86  Simplification rules
% 4.68/1.86  ----------------------
% 4.68/1.86  #Subsume      : 185
% 4.68/1.86  #Demod        : 1226
% 4.68/1.86  #Tautology    : 705
% 4.68/1.86  #SimpNegUnit  : 54
% 4.68/1.86  #BackRed      : 8
% 4.68/1.86  
% 4.68/1.86  #Partial instantiations: 0
% 4.68/1.86  #Strategies tried      : 1
% 4.68/1.86  
% 4.68/1.86  Timing (in seconds)
% 4.68/1.86  ----------------------
% 4.68/1.86  Preprocessing        : 0.29
% 4.68/1.86  Parsing              : 0.15
% 4.68/1.86  CNF conversion       : 0.02
% 4.68/1.86  Main loop            : 0.80
% 4.68/1.86  Inferencing          : 0.27
% 4.68/1.86  Reduction            : 0.30
% 4.68/1.86  Demodulation         : 0.24
% 4.68/1.86  BG Simplification    : 0.03
% 4.68/1.86  Subsumption          : 0.15
% 4.68/1.86  Abstraction          : 0.04
% 4.68/1.86  MUC search           : 0.00
% 4.68/1.86  Cooper               : 0.00
% 4.68/1.86  Total                : 1.12
% 4.68/1.86  Index Insertion      : 0.00
% 4.68/1.86  Index Deletion       : 0.00
% 4.68/1.86  Index Matching       : 0.00
% 4.68/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
