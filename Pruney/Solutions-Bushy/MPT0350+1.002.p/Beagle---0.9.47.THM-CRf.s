%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0350+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:08 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  103 (1014 expanded)
%              Number of leaves         :   29 ( 327 expanded)
%              Depth                    :   21
%              Number of atoms          :  152 (2111 expanded)
%              Number of equality atoms :   50 ( 484 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_64,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_24,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_43,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,(
    ! [B_34,A_35] :
      ( v1_xboole_0(B_34)
      | ~ m1_subset_1(B_34,A_35)
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_169,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_161])).

tff(c_170,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_214,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_223,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_214])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_227,plain,
    ( k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_36])).

tff(c_231,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_181,plain,(
    ! [B_40,A_41] :
      ( r2_hidden(B_40,A_41)
      | ~ m1_subset_1(B_40,A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_251,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(B_52,A_53)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | v1_xboole_0(k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_264,plain,
    ( r1_tarski('#skF_4','#skF_3')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_251])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_231,c_264])).

tff(c_272,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_287,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_181,c_4])).

tff(c_298,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(k3_subset_1(A_13,B_14),A_13)
      | v1_xboole_0(k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_28,c_287])).

tff(c_278,plain,(
    ! [A_54,B_55] :
      ( m1_subset_1(k3_subset_1(A_54,B_55),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_497,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,k3_subset_1(A_92,B_93)) = k3_subset_1(A_92,k3_subset_1(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(resolution,[status(thm)],[c_278,c_26])).

tff(c_510,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_497])).

tff(c_514,plain,
    ( k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4'))) = '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_36])).

tff(c_605,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_514])).

tff(c_608,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_298,c_605])).

tff(c_611,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_608])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_611])).

tff(c_615,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_514])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    ! [B_38,A_39] :
      ( m1_subset_1(B_38,A_39)
      | ~ r2_hidden(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_180,plain,(
    ! [C_7,A_3] :
      ( m1_subset_1(C_7,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_415,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_953,plain,(
    ! [A_130,B_131,C_132] :
      ( k4_subset_1(A_130,B_131,C_132) = k2_xboole_0(B_131,C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130))
      | v1_xboole_0(k1_zfmisc_1(A_130))
      | ~ r1_tarski(C_132,A_130) ) ),
    inference(resolution,[status(thm)],[c_180,c_415])).

tff(c_968,plain,(
    ! [C_132] :
      ( k4_subset_1('#skF_3','#skF_4',C_132) = k2_xboole_0('#skF_4',C_132)
      | v1_xboole_0(k1_zfmisc_1('#skF_3'))
      | ~ r1_tarski(C_132,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_953])).

tff(c_977,plain,(
    ! [C_133] :
      ( k4_subset_1('#skF_3','#skF_4',C_133) = k2_xboole_0('#skF_4',C_133)
      | ~ r1_tarski(C_133,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_968])).

tff(c_994,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_615,c_977])).

tff(c_1013,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_994])).

tff(c_1015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_1013])).

tff(c_1016,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_1017,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_38,plain,(
    ! [A_22] :
      ( k1_xboole_0 = A_22
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1021,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1016,c_38])).

tff(c_1104,plain,(
    ! [A_139] :
      ( A_139 = '#skF_4'
      | ~ v1_xboole_0(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_38])).

tff(c_1111,plain,(
    k1_zfmisc_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1017,c_1104])).

tff(c_1115,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_42])).

tff(c_34,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1025,plain,(
    ! [A_19] : k4_xboole_0(A_19,'#skF_4') = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_34])).

tff(c_1192,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k3_subset_1(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1201,plain,(
    ! [B_150] :
      ( k4_xboole_0('#skF_3',B_150) = k3_subset_1('#skF_3',B_150)
      | ~ m1_subset_1(B_150,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_1192])).

tff(c_1204,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1115,c_1201])).

tff(c_1210,plain,(
    k3_subset_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1025,c_1204])).

tff(c_1225,plain,(
    ! [A_152,B_153] :
      ( m1_subset_1(k3_subset_1(A_152,B_153),k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1234,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_1225])).

tff(c_1241,plain,(
    m1_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1111,c_1111,c_1234])).

tff(c_22,plain,(
    ! [B_9,A_8] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,A_8)
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1248,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1241,c_22])).

tff(c_1252,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1248])).

tff(c_1023,plain,(
    ! [A_22] :
      ( A_22 = '#skF_4'
      | ~ v1_xboole_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_38])).

tff(c_1275,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1252,c_1023])).

tff(c_1214,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1210,c_43])).

tff(c_1279,plain,(
    k4_subset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_1275,c_1275,c_1214])).

tff(c_32,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1024,plain,(
    ! [A_18] : k2_xboole_0(A_18,'#skF_4') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_32])).

tff(c_1284,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1275,c_1111])).

tff(c_1684,plain,(
    ! [A_195,B_196,C_197] :
      ( k4_subset_1(A_195,B_196,C_197) = k2_xboole_0(B_196,C_197)
      | ~ m1_subset_1(C_197,k1_zfmisc_1(A_195))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1688,plain,(
    ! [B_196,C_197] :
      ( k4_subset_1('#skF_4',B_196,C_197) = k2_xboole_0(B_196,C_197)
      | ~ m1_subset_1(C_197,'#skF_4')
      | ~ m1_subset_1(B_196,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1284,c_1684])).

tff(c_1805,plain,(
    ! [B_207,C_208] :
      ( k4_subset_1('#skF_4',B_207,C_208) = k2_xboole_0(B_207,C_208)
      | ~ m1_subset_1(C_208,'#skF_4')
      | ~ m1_subset_1(B_207,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1688])).

tff(c_1809,plain,(
    ! [B_207] :
      ( k4_subset_1('#skF_4',B_207,'#skF_4') = k2_xboole_0(B_207,'#skF_4')
      | ~ m1_subset_1(B_207,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1115,c_1805])).

tff(c_1819,plain,(
    ! [B_209] :
      ( k4_subset_1('#skF_4',B_209,'#skF_4') = B_209
      | ~ m1_subset_1(B_209,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_1809])).

tff(c_1825,plain,(
    k4_subset_1('#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1115,c_1819])).

tff(c_1834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1279,c_1825])).

%------------------------------------------------------------------------------
