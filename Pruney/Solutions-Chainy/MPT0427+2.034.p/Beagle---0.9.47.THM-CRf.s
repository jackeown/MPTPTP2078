%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:01 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 334 expanded)
%              Number of equality atoms :   36 ( 129 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_321,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k8_setfam_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_437,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k8_setfam_1(A_98,B_99),A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(resolution,[status(thm)],[c_321,c_38])).

tff(c_458,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_437])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_179,plain,(
    ! [A_64,B_65] :
      ( k6_setfam_1(A_64,B_65) = k1_setfam_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_195,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_179])).

tff(c_1246,plain,(
    ! [A_138,B_139] :
      ( k8_setfam_1(A_138,B_139) = k6_setfam_1(A_138,B_139)
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(A_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1268,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_1246])).

tff(c_1283,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1268])).

tff(c_1289,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_26,plain,(
    ! [A_17] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_18] :
      ( k8_setfam_1(A_18,k1_xboole_0) = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [A_18] : k8_setfam_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28])).

tff(c_1302,plain,(
    ! [A_18] : k8_setfam_1(A_18,'#skF_4') = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_54])).

tff(c_46,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1416,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1302,c_46])).

tff(c_1420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_1416])).

tff(c_1422,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_48,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    ! [B_32,A_31] :
      ( r1_tarski(k1_setfam_1(B_32),k1_setfam_1(A_31))
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_196,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_179])).

tff(c_1271,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_1246])).

tff(c_1285,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_1271])).

tff(c_1458,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_1459,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_1422])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1474,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_6])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(k1_zfmisc_1(A_14),k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_265,plain,(
    ! [A_71,C_72,B_73] :
      ( m1_subset_1(A_71,C_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(C_72))
      | ~ r2_hidden(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_407,plain,(
    ! [A_91,B_92,A_93] :
      ( m1_subset_1(A_91,B_92)
      | ~ r2_hidden(A_91,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_40,c_265])).

tff(c_941,plain,(
    ! [C_118,B_119,A_120] :
      ( m1_subset_1(C_118,B_119)
      | ~ r1_tarski(k1_zfmisc_1(A_120),B_119)
      | ~ r1_tarski(C_118,A_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_407])).

tff(c_1047,plain,(
    ! [C_129,B_130,A_131] :
      ( m1_subset_1(C_129,k1_zfmisc_1(B_130))
      | ~ r1_tarski(C_129,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(resolution,[status(thm)],[c_22,c_941])).

tff(c_1100,plain,(
    ! [B_132] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(B_132))
      | ~ r1_tarski('#skF_5',B_132) ) ),
    inference(resolution,[status(thm)],[c_48,c_1047])).

tff(c_1116,plain,(
    ! [B_132] :
      ( r1_tarski('#skF_4',B_132)
      | ~ r1_tarski('#skF_5',B_132) ) ),
    inference(resolution,[status(thm)],[c_1100,c_38])).

tff(c_1482,plain,(
    ! [B_132] : r1_tarski('#skF_4',B_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1474,c_1116])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1917,plain,(
    ! [A_159,B_160] :
      ( A_159 = '#skF_5'
      | ~ r1_tarski(A_159,k4_xboole_0(B_160,A_159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1458,c_8])).

tff(c_1933,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1482,c_1917])).

tff(c_1944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1459,c_1933])).

tff(c_1945,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_1421,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1425,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_46])).

tff(c_1947,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_1425])).

tff(c_1975,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1947])).

tff(c_1978,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1975])).

tff(c_1980,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1422,c_1978])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.71/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.61  
% 3.71/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.62  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.71/1.62  
% 3.71/1.62  %Foreground sorts:
% 3.71/1.62  
% 3.71/1.62  
% 3.71/1.62  %Background operators:
% 3.71/1.62  
% 3.71/1.62  
% 3.71/1.62  %Foreground operators:
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.71/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.71/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.71/1.62  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.71/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.71/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.62  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.71/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.71/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.71/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.71/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.71/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.62  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.71/1.62  
% 3.71/1.63  tff(f_106, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.71/1.63  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.71/1.63  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.71/1.63  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.71/1.63  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.71/1.63  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.71/1.63  tff(f_96, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.71/1.63  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.71/1.63  tff(f_50, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 3.71/1.63  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.71/1.63  tff(f_90, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.71/1.63  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.71/1.63  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.63  tff(c_321, plain, (![A_82, B_83]: (m1_subset_1(k8_setfam_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.63  tff(c_38, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.71/1.63  tff(c_437, plain, (![A_98, B_99]: (r1_tarski(k8_setfam_1(A_98, B_99), A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(resolution, [status(thm)], [c_321, c_38])).
% 3.71/1.63  tff(c_458, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_50, c_437])).
% 3.71/1.63  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.63  tff(c_179, plain, (![A_64, B_65]: (k6_setfam_1(A_64, B_65)=k1_setfam_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.71/1.63  tff(c_195, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_179])).
% 3.71/1.63  tff(c_1246, plain, (![A_138, B_139]: (k8_setfam_1(A_138, B_139)=k6_setfam_1(A_138, B_139) | k1_xboole_0=B_139 | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(A_138))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.71/1.63  tff(c_1268, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_52, c_1246])).
% 3.71/1.63  tff(c_1283, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1268])).
% 3.71/1.63  tff(c_1289, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1283])).
% 3.71/1.63  tff(c_26, plain, (![A_17]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.71/1.63  tff(c_28, plain, (![A_18]: (k8_setfam_1(A_18, k1_xboole_0)=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.71/1.63  tff(c_54, plain, (![A_18]: (k8_setfam_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28])).
% 3.71/1.63  tff(c_1302, plain, (![A_18]: (k8_setfam_1(A_18, '#skF_4')=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_1289, c_54])).
% 3.71/1.63  tff(c_46, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.63  tff(c_1416, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1302, c_46])).
% 3.71/1.63  tff(c_1420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_1416])).
% 3.71/1.63  tff(c_1422, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1283])).
% 3.71/1.63  tff(c_48, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.71/1.63  tff(c_44, plain, (![B_32, A_31]: (r1_tarski(k1_setfam_1(B_32), k1_setfam_1(A_31)) | k1_xboole_0=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.71/1.63  tff(c_196, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_50, c_179])).
% 3.71/1.63  tff(c_1271, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_1246])).
% 3.71/1.63  tff(c_1285, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_1271])).
% 3.71/1.63  tff(c_1458, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1285])).
% 3.71/1.63  tff(c_1459, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_1422])).
% 3.71/1.63  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.71/1.63  tff(c_1474, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_6])).
% 3.71/1.63  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(k1_zfmisc_1(A_14), k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.71/1.63  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.71/1.63  tff(c_40, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.71/1.63  tff(c_265, plain, (![A_71, C_72, B_73]: (m1_subset_1(A_71, C_72) | ~m1_subset_1(B_73, k1_zfmisc_1(C_72)) | ~r2_hidden(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.71/1.63  tff(c_407, plain, (![A_91, B_92, A_93]: (m1_subset_1(A_91, B_92) | ~r2_hidden(A_91, A_93) | ~r1_tarski(A_93, B_92))), inference(resolution, [status(thm)], [c_40, c_265])).
% 3.71/1.63  tff(c_941, plain, (![C_118, B_119, A_120]: (m1_subset_1(C_118, B_119) | ~r1_tarski(k1_zfmisc_1(A_120), B_119) | ~r1_tarski(C_118, A_120))), inference(resolution, [status(thm)], [c_12, c_407])).
% 3.71/1.63  tff(c_1047, plain, (![C_129, B_130, A_131]: (m1_subset_1(C_129, k1_zfmisc_1(B_130)) | ~r1_tarski(C_129, A_131) | ~r1_tarski(A_131, B_130))), inference(resolution, [status(thm)], [c_22, c_941])).
% 3.71/1.63  tff(c_1100, plain, (![B_132]: (m1_subset_1('#skF_4', k1_zfmisc_1(B_132)) | ~r1_tarski('#skF_5', B_132))), inference(resolution, [status(thm)], [c_48, c_1047])).
% 3.71/1.63  tff(c_1116, plain, (![B_132]: (r1_tarski('#skF_4', B_132) | ~r1_tarski('#skF_5', B_132))), inference(resolution, [status(thm)], [c_1100, c_38])).
% 3.71/1.63  tff(c_1482, plain, (![B_132]: (r1_tarski('#skF_4', B_132))), inference(demodulation, [status(thm), theory('equality')], [c_1474, c_1116])).
% 3.71/1.63  tff(c_8, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.71/1.63  tff(c_1917, plain, (![A_159, B_160]: (A_159='#skF_5' | ~r1_tarski(A_159, k4_xboole_0(B_160, A_159)))), inference(demodulation, [status(thm), theory('equality')], [c_1458, c_8])).
% 3.71/1.63  tff(c_1933, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1482, c_1917])).
% 3.71/1.63  tff(c_1944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1459, c_1933])).
% 3.71/1.63  tff(c_1945, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_1285])).
% 3.71/1.63  tff(c_1421, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_1283])).
% 3.71/1.63  tff(c_1425, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_46])).
% 3.71/1.63  tff(c_1947, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_1425])).
% 3.71/1.63  tff(c_1975, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_1947])).
% 3.71/1.63  tff(c_1978, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1975])).
% 3.71/1.63  tff(c_1980, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1422, c_1978])).
% 3.71/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.63  
% 3.71/1.63  Inference rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Ref     : 0
% 3.71/1.63  #Sup     : 408
% 3.71/1.63  #Fact    : 0
% 3.71/1.63  #Define  : 0
% 3.71/1.63  #Split   : 9
% 3.71/1.63  #Chain   : 0
% 3.71/1.63  #Close   : 0
% 3.71/1.63  
% 3.71/1.63  Ordering : KBO
% 3.71/1.63  
% 3.71/1.63  Simplification rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Subsume      : 49
% 3.71/1.63  #Demod        : 269
% 3.71/1.63  #Tautology    : 182
% 3.71/1.63  #SimpNegUnit  : 3
% 3.71/1.63  #BackRed      : 63
% 3.71/1.63  
% 3.71/1.63  #Partial instantiations: 0
% 3.71/1.63  #Strategies tried      : 1
% 3.71/1.63  
% 3.71/1.63  Timing (in seconds)
% 3.71/1.63  ----------------------
% 3.87/1.64  Preprocessing        : 0.32
% 3.87/1.64  Parsing              : 0.17
% 3.87/1.64  CNF conversion       : 0.02
% 3.87/1.64  Main loop            : 0.54
% 3.87/1.64  Inferencing          : 0.18
% 3.87/1.64  Reduction            : 0.18
% 3.87/1.64  Demodulation         : 0.12
% 3.87/1.64  BG Simplification    : 0.02
% 3.87/1.64  Subsumption          : 0.11
% 3.87/1.64  Abstraction          : 0.03
% 3.87/1.64  MUC search           : 0.00
% 3.87/1.64  Cooper               : 0.00
% 3.87/1.64  Total                : 0.89
% 3.87/1.64  Index Insertion      : 0.00
% 3.87/1.64  Index Deletion       : 0.00
% 3.87/1.64  Index Matching       : 0.00
% 3.87/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
