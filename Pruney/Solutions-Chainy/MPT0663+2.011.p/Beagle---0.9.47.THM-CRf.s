%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:12 EST 2020

% Result     : Theorem 23.12s
% Output     : CNFRefutation 23.12s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 119 expanded)
%              Number of leaves         :   46 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  108 ( 171 expanded)
%              Number of equality atoms :   48 (  86 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_103,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_enumset1(D,C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_116,plain,(
    r2_hidden('#skF_7',k3_xboole_0(k1_relat_1('#skF_9'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [A_96,B_97,C_98] : k2_xboole_0(k2_tarski(A_96,B_97),C_98) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_96,B_97] : k2_tarski(A_96,B_97) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_144])).

tff(c_104,plain,(
    ! [A_86,B_87] : k1_setfam_1(k2_tarski(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_12,plain,(
    ! [A_23,B_24] : k1_enumset1(A_23,A_23,B_24) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_229,plain,(
    ! [D_115,C_116,B_117,A_118] : k2_enumset1(D_115,C_116,B_117,A_118) = k2_enumset1(A_118,B_117,C_116,D_115) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_25,B_26,C_27] : k2_enumset1(A_25,A_25,B_26,C_27) = k1_enumset1(A_25,B_26,C_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_245,plain,(
    ! [D_115,C_116,B_117] : k2_enumset1(D_115,C_116,B_117,B_117) = k1_enumset1(B_117,C_116,D_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_14])).

tff(c_16,plain,(
    ! [A_28,B_29,C_30,D_31] : k3_enumset1(A_28,A_28,B_29,C_30,D_31) = k2_enumset1(A_28,B_29,C_30,D_31) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [B_33,C_34,E_36,A_32,D_35] : k4_enumset1(A_32,A_32,B_33,C_34,D_35,E_36) = k3_enumset1(A_32,B_33,C_34,D_35,E_36) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] : k5_enumset1(A_37,A_37,B_38,C_39,D_40,E_41,F_42) = k4_enumset1(A_37,B_38,C_39,D_40,E_41,F_42) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56483,plain,(
    ! [G_3722,C_3723,B_3727,F_3725,E_3728,D_3724,A_3726] : k6_enumset1(A_3726,A_3726,B_3727,C_3723,D_3724,E_3728,F_3725,G_3722) = k5_enumset1(A_3726,B_3727,C_3723,D_3724,E_3728,F_3725,G_3722) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [B_56,J_66,E_59,G_61,H_62,A_55,F_60,D_58] : r2_hidden(J_66,k6_enumset1(A_55,B_56,J_66,D_58,E_59,F_60,G_61,H_62)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_56516,plain,(
    ! [A_3733,F_3732,B_3729,G_3735,D_3730,C_3731,E_3734] : r2_hidden(B_3729,k5_enumset1(A_3733,B_3729,C_3731,D_3730,E_3734,F_3732,G_3735)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56483,c_40])).

tff(c_56523,plain,(
    ! [B_3737,D_3739,C_3741,E_3740,F_3738,A_3736] : r2_hidden(A_3736,k4_enumset1(A_3736,B_3737,C_3741,D_3739,E_3740,F_3738)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_56516])).

tff(c_56605,plain,(
    ! [E_3745,A_3748,C_3747,D_3749,B_3746] : r2_hidden(A_3748,k3_enumset1(A_3748,B_3746,C_3747,D_3749,E_3745)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_56523])).

tff(c_56612,plain,(
    ! [A_3750,B_3751,C_3752,D_3753] : r2_hidden(A_3750,k2_enumset1(A_3750,B_3751,C_3752,D_3753)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_56605])).

tff(c_56628,plain,(
    ! [D_3754,B_3755,C_3756] : r2_hidden(D_3754,k1_enumset1(B_3755,C_3756,D_3754)) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_56612])).

tff(c_56642,plain,(
    ! [B_3757,A_3758] : r2_hidden(B_3757,k2_tarski(A_3758,B_3757)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56628])).

tff(c_94,plain,(
    ! [C_79,D_82,A_67] :
      ( r2_hidden(C_79,D_82)
      | ~ r2_hidden(D_82,A_67)
      | ~ r2_hidden(C_79,k1_setfam_1(A_67))
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56644,plain,(
    ! [C_79,B_3757,A_3758] :
      ( r2_hidden(C_79,B_3757)
      | ~ r2_hidden(C_79,k1_setfam_1(k2_tarski(A_3758,B_3757)))
      | k2_tarski(A_3758,B_3757) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56642,c_94])).

tff(c_56649,plain,(
    ! [C_79,B_3757,A_3758] :
      ( r2_hidden(C_79,B_3757)
      | ~ r2_hidden(C_79,k3_xboole_0(A_3758,B_3757))
      | k2_tarski(A_3758,B_3757) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56644])).

tff(c_56771,plain,(
    ! [C_3781,B_3782,A_3783] :
      ( r2_hidden(C_3781,B_3782)
      | ~ r2_hidden(C_3781,k3_xboole_0(A_3783,B_3782)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_56649])).

tff(c_56802,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_116,c_56771])).

tff(c_120,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_118,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56657,plain,(
    ! [A_3760,B_3761,C_3762] : r2_hidden(A_3760,k1_enumset1(A_3760,B_3761,C_3762)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_56612])).

tff(c_56672,plain,(
    ! [A_3763,B_3764] : r2_hidden(A_3763,k2_tarski(A_3763,B_3764)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56657])).

tff(c_56674,plain,(
    ! [C_79,A_3763,B_3764] :
      ( r2_hidden(C_79,A_3763)
      | ~ r2_hidden(C_79,k1_setfam_1(k2_tarski(A_3763,B_3764)))
      | k2_tarski(A_3763,B_3764) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56672,c_94])).

tff(c_56679,plain,(
    ! [C_79,A_3763,B_3764] :
      ( r2_hidden(C_79,A_3763)
      | ~ r2_hidden(C_79,k3_xboole_0(A_3763,B_3764))
      | k2_tarski(A_3763,B_3764) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_56674])).

tff(c_56736,plain,(
    ! [C_3778,A_3779,B_3780] :
      ( r2_hidden(C_3778,A_3779)
      | ~ r2_hidden(C_3778,k3_xboole_0(A_3779,B_3780)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_56679])).

tff(c_56767,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_116,c_56736])).

tff(c_106,plain,(
    ! [A_88,C_90,B_89] :
      ( r2_hidden(A_88,k1_relat_1(k7_relat_1(C_90,B_89)))
      | ~ r2_hidden(A_88,k1_relat_1(C_90))
      | ~ r2_hidden(A_88,B_89)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_73477,plain,(
    ! [C_4874,B_4875,A_4876] :
      ( k1_funct_1(k7_relat_1(C_4874,B_4875),A_4876) = k1_funct_1(C_4874,A_4876)
      | ~ r2_hidden(A_4876,k1_relat_1(k7_relat_1(C_4874,B_4875)))
      | ~ v1_funct_1(C_4874)
      | ~ v1_relat_1(C_4874) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_88297,plain,(
    ! [C_5839,B_5840,A_5841] :
      ( k1_funct_1(k7_relat_1(C_5839,B_5840),A_5841) = k1_funct_1(C_5839,A_5841)
      | ~ v1_funct_1(C_5839)
      | ~ r2_hidden(A_5841,k1_relat_1(C_5839))
      | ~ r2_hidden(A_5841,B_5840)
      | ~ v1_relat_1(C_5839) ) ),
    inference(resolution,[status(thm)],[c_106,c_73477])).

tff(c_88335,plain,(
    ! [B_5840] :
      ( k1_funct_1(k7_relat_1('#skF_9',B_5840),'#skF_7') = k1_funct_1('#skF_9','#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ r2_hidden('#skF_7',B_5840)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_56767,c_88297])).

tff(c_88361,plain,(
    ! [B_5842] :
      ( k1_funct_1(k7_relat_1('#skF_9',B_5842),'#skF_7') = k1_funct_1('#skF_9','#skF_7')
      | ~ r2_hidden('#skF_7',B_5842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_118,c_88335])).

tff(c_114,plain,(
    k1_funct_1(k7_relat_1('#skF_9','#skF_8'),'#skF_7') != k1_funct_1('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_88367,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_88361,c_114])).

tff(c_88375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56802,c_88367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.12/14.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.12/14.22  
% 23.12/14.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.12/14.23  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 23.12/14.23  
% 23.12/14.23  %Foreground sorts:
% 23.12/14.23  
% 23.12/14.23  
% 23.12/14.23  %Background operators:
% 23.12/14.23  
% 23.12/14.23  
% 23.12/14.23  %Foreground operators:
% 23.12/14.23  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 23.12/14.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.12/14.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.12/14.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.12/14.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.12/14.23  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.12/14.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.12/14.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff('#skF_7', type, '#skF_7': $i).
% 23.12/14.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.12/14.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.12/14.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.12/14.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff('#skF_9', type, '#skF_9': $i).
% 23.12/14.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 23.12/14.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff('#skF_8', type, '#skF_8': $i).
% 23.12/14.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.12/14.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 23.12/14.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.12/14.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 23.12/14.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.12/14.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.12/14.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.12/14.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 23.12/14.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 23.12/14.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.12/14.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.12/14.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 23.12/14.23  
% 23.12/14.24  tff(f_128, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_funct_1)).
% 23.12/14.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 23.12/14.24  tff(f_52, axiom, (![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 23.12/14.24  tff(f_103, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 23.12/14.24  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 23.12/14.24  tff(f_29, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_enumset1(D, C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_enumset1)).
% 23.12/14.24  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 23.12/14.24  tff(f_41, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 23.12/14.24  tff(f_43, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 23.12/14.24  tff(f_45, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 23.12/14.24  tff(f_47, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 23.12/14.24  tff(f_82, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_enumset1)).
% 23.12/14.24  tff(f_101, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 23.12/14.24  tff(f_111, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 23.12/14.24  tff(f_119, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 23.12/14.24  tff(c_116, plain, (r2_hidden('#skF_7', k3_xboole_0(k1_relat_1('#skF_9'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.12/14.24  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.12/14.24  tff(c_144, plain, (![A_96, B_97, C_98]: (k2_xboole_0(k2_tarski(A_96, B_97), C_98)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.12/14.24  tff(c_150, plain, (![A_96, B_97]: (k2_tarski(A_96, B_97)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_144])).
% 23.12/14.24  tff(c_104, plain, (![A_86, B_87]: (k1_setfam_1(k2_tarski(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.12/14.24  tff(c_12, plain, (![A_23, B_24]: (k1_enumset1(A_23, A_23, B_24)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.12/14.24  tff(c_229, plain, (![D_115, C_116, B_117, A_118]: (k2_enumset1(D_115, C_116, B_117, A_118)=k2_enumset1(A_118, B_117, C_116, D_115))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.12/14.24  tff(c_14, plain, (![A_25, B_26, C_27]: (k2_enumset1(A_25, A_25, B_26, C_27)=k1_enumset1(A_25, B_26, C_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.12/14.24  tff(c_245, plain, (![D_115, C_116, B_117]: (k2_enumset1(D_115, C_116, B_117, B_117)=k1_enumset1(B_117, C_116, D_115))), inference(superposition, [status(thm), theory('equality')], [c_229, c_14])).
% 23.12/14.24  tff(c_16, plain, (![A_28, B_29, C_30, D_31]: (k3_enumset1(A_28, A_28, B_29, C_30, D_31)=k2_enumset1(A_28, B_29, C_30, D_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.12/14.24  tff(c_18, plain, (![B_33, C_34, E_36, A_32, D_35]: (k4_enumset1(A_32, A_32, B_33, C_34, D_35, E_36)=k3_enumset1(A_32, B_33, C_34, D_35, E_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.12/14.24  tff(c_20, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (k5_enumset1(A_37, A_37, B_38, C_39, D_40, E_41, F_42)=k4_enumset1(A_37, B_38, C_39, D_40, E_41, F_42))), inference(cnfTransformation, [status(thm)], [f_45])).
% 23.12/14.24  tff(c_56483, plain, (![G_3722, C_3723, B_3727, F_3725, E_3728, D_3724, A_3726]: (k6_enumset1(A_3726, A_3726, B_3727, C_3723, D_3724, E_3728, F_3725, G_3722)=k5_enumset1(A_3726, B_3727, C_3723, D_3724, E_3728, F_3725, G_3722))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.12/14.24  tff(c_40, plain, (![B_56, J_66, E_59, G_61, H_62, A_55, F_60, D_58]: (r2_hidden(J_66, k6_enumset1(A_55, B_56, J_66, D_58, E_59, F_60, G_61, H_62)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.12/14.24  tff(c_56516, plain, (![A_3733, F_3732, B_3729, G_3735, D_3730, C_3731, E_3734]: (r2_hidden(B_3729, k5_enumset1(A_3733, B_3729, C_3731, D_3730, E_3734, F_3732, G_3735)))), inference(superposition, [status(thm), theory('equality')], [c_56483, c_40])).
% 23.12/14.24  tff(c_56523, plain, (![B_3737, D_3739, C_3741, E_3740, F_3738, A_3736]: (r2_hidden(A_3736, k4_enumset1(A_3736, B_3737, C_3741, D_3739, E_3740, F_3738)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_56516])).
% 23.12/14.24  tff(c_56605, plain, (![E_3745, A_3748, C_3747, D_3749, B_3746]: (r2_hidden(A_3748, k3_enumset1(A_3748, B_3746, C_3747, D_3749, E_3745)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_56523])).
% 23.12/14.24  tff(c_56612, plain, (![A_3750, B_3751, C_3752, D_3753]: (r2_hidden(A_3750, k2_enumset1(A_3750, B_3751, C_3752, D_3753)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_56605])).
% 23.12/14.24  tff(c_56628, plain, (![D_3754, B_3755, C_3756]: (r2_hidden(D_3754, k1_enumset1(B_3755, C_3756, D_3754)))), inference(superposition, [status(thm), theory('equality')], [c_245, c_56612])).
% 23.12/14.24  tff(c_56642, plain, (![B_3757, A_3758]: (r2_hidden(B_3757, k2_tarski(A_3758, B_3757)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56628])).
% 23.12/14.24  tff(c_94, plain, (![C_79, D_82, A_67]: (r2_hidden(C_79, D_82) | ~r2_hidden(D_82, A_67) | ~r2_hidden(C_79, k1_setfam_1(A_67)) | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_101])).
% 23.12/14.24  tff(c_56644, plain, (![C_79, B_3757, A_3758]: (r2_hidden(C_79, B_3757) | ~r2_hidden(C_79, k1_setfam_1(k2_tarski(A_3758, B_3757))) | k2_tarski(A_3758, B_3757)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56642, c_94])).
% 23.12/14.24  tff(c_56649, plain, (![C_79, B_3757, A_3758]: (r2_hidden(C_79, B_3757) | ~r2_hidden(C_79, k3_xboole_0(A_3758, B_3757)) | k2_tarski(A_3758, B_3757)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56644])).
% 23.12/14.24  tff(c_56771, plain, (![C_3781, B_3782, A_3783]: (r2_hidden(C_3781, B_3782) | ~r2_hidden(C_3781, k3_xboole_0(A_3783, B_3782)))), inference(negUnitSimplification, [status(thm)], [c_150, c_56649])).
% 23.12/14.24  tff(c_56802, plain, (r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_116, c_56771])).
% 23.12/14.24  tff(c_120, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.12/14.24  tff(c_118, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.12/14.24  tff(c_56657, plain, (![A_3760, B_3761, C_3762]: (r2_hidden(A_3760, k1_enumset1(A_3760, B_3761, C_3762)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_56612])).
% 23.12/14.24  tff(c_56672, plain, (![A_3763, B_3764]: (r2_hidden(A_3763, k2_tarski(A_3763, B_3764)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56657])).
% 23.12/14.24  tff(c_56674, plain, (![C_79, A_3763, B_3764]: (r2_hidden(C_79, A_3763) | ~r2_hidden(C_79, k1_setfam_1(k2_tarski(A_3763, B_3764))) | k2_tarski(A_3763, B_3764)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56672, c_94])).
% 23.12/14.24  tff(c_56679, plain, (![C_79, A_3763, B_3764]: (r2_hidden(C_79, A_3763) | ~r2_hidden(C_79, k3_xboole_0(A_3763, B_3764)) | k2_tarski(A_3763, B_3764)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_104, c_56674])).
% 23.12/14.24  tff(c_56736, plain, (![C_3778, A_3779, B_3780]: (r2_hidden(C_3778, A_3779) | ~r2_hidden(C_3778, k3_xboole_0(A_3779, B_3780)))), inference(negUnitSimplification, [status(thm)], [c_150, c_56679])).
% 23.12/14.24  tff(c_56767, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_116, c_56736])).
% 23.12/14.24  tff(c_106, plain, (![A_88, C_90, B_89]: (r2_hidden(A_88, k1_relat_1(k7_relat_1(C_90, B_89))) | ~r2_hidden(A_88, k1_relat_1(C_90)) | ~r2_hidden(A_88, B_89) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_111])).
% 23.12/14.24  tff(c_73477, plain, (![C_4874, B_4875, A_4876]: (k1_funct_1(k7_relat_1(C_4874, B_4875), A_4876)=k1_funct_1(C_4874, A_4876) | ~r2_hidden(A_4876, k1_relat_1(k7_relat_1(C_4874, B_4875))) | ~v1_funct_1(C_4874) | ~v1_relat_1(C_4874))), inference(cnfTransformation, [status(thm)], [f_119])).
% 23.12/14.24  tff(c_88297, plain, (![C_5839, B_5840, A_5841]: (k1_funct_1(k7_relat_1(C_5839, B_5840), A_5841)=k1_funct_1(C_5839, A_5841) | ~v1_funct_1(C_5839) | ~r2_hidden(A_5841, k1_relat_1(C_5839)) | ~r2_hidden(A_5841, B_5840) | ~v1_relat_1(C_5839))), inference(resolution, [status(thm)], [c_106, c_73477])).
% 23.12/14.24  tff(c_88335, plain, (![B_5840]: (k1_funct_1(k7_relat_1('#skF_9', B_5840), '#skF_7')=k1_funct_1('#skF_9', '#skF_7') | ~v1_funct_1('#skF_9') | ~r2_hidden('#skF_7', B_5840) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_56767, c_88297])).
% 23.12/14.24  tff(c_88361, plain, (![B_5842]: (k1_funct_1(k7_relat_1('#skF_9', B_5842), '#skF_7')=k1_funct_1('#skF_9', '#skF_7') | ~r2_hidden('#skF_7', B_5842))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_118, c_88335])).
% 23.12/14.24  tff(c_114, plain, (k1_funct_1(k7_relat_1('#skF_9', '#skF_8'), '#skF_7')!=k1_funct_1('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.12/14.24  tff(c_88367, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_88361, c_114])).
% 23.12/14.24  tff(c_88375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56802, c_88367])).
% 23.12/14.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.12/14.24  
% 23.12/14.24  Inference rules
% 23.12/14.24  ----------------------
% 23.12/14.24  #Ref     : 0
% 23.12/14.24  #Sup     : 21329
% 23.12/14.24  #Fact    : 6
% 23.12/14.24  #Define  : 0
% 23.12/14.24  #Split   : 20
% 23.12/14.24  #Chain   : 0
% 23.12/14.24  #Close   : 0
% 23.12/14.24  
% 23.12/14.24  Ordering : KBO
% 23.12/14.24  
% 23.12/14.24  Simplification rules
% 23.12/14.24  ----------------------
% 23.12/14.24  #Subsume      : 5312
% 23.12/14.24  #Demod        : 13640
% 23.12/14.24  #Tautology    : 9812
% 23.12/14.24  #SimpNegUnit  : 714
% 23.12/14.24  #BackRed      : 190
% 23.12/14.24  
% 23.12/14.24  #Partial instantiations: 0
% 23.12/14.24  #Strategies tried      : 1
% 23.12/14.24  
% 23.12/14.24  Timing (in seconds)
% 23.12/14.24  ----------------------
% 23.12/14.25  Preprocessing        : 0.39
% 23.12/14.25  Parsing              : 0.19
% 23.12/14.25  CNF conversion       : 0.03
% 23.12/14.25  Main loop            : 13.09
% 23.12/14.25  Inferencing          : 2.91
% 23.12/14.25  Reduction            : 6.22
% 23.12/14.25  Demodulation         : 5.48
% 23.12/14.25  BG Simplification    : 0.27
% 23.12/14.25  Subsumption          : 3.10
% 23.12/14.25  Abstraction          : 0.56
% 23.12/14.25  MUC search           : 0.00
% 23.12/14.25  Cooper               : 0.00
% 23.12/14.25  Total                : 13.52
% 23.12/14.25  Index Insertion      : 0.00
% 23.12/14.25  Index Deletion       : 0.00
% 23.12/14.25  Index Matching       : 0.00
% 23.12/14.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
