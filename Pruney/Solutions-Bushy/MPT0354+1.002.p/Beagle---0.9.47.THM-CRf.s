%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0354+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:09 EST 2020

% Result     : Theorem 45.63s
% Output     : CNFRefutation 45.63s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 519 expanded)
%              Number of leaves         :   33 ( 185 expanded)
%              Depth                    :   22
%              Number of atoms          :  114 ( 631 expanded)
%              Number of equality atoms :   75 ( 343 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_subset_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_26,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_28,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_64,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_70,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_277,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_277])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_18,plain,(
    ! [A_20,B_21] : k6_subset_1(A_20,B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8] : m1_subset_1(k6_subset_1(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_37,plain,(
    ! [A_7,B_8] : m1_subset_1(k4_xboole_0(A_7,B_8),k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_999,plain,(
    ! [A_94,B_95,C_96] :
      ( k4_subset_1(A_94,B_95,C_96) = k2_xboole_0(B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1657,plain,(
    ! [B_118] :
      ( k4_subset_1('#skF_1',B_118,'#skF_3') = k2_xboole_0(B_118,'#skF_3')
      | ~ m1_subset_1(B_118,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_999])).

tff(c_1709,plain,(
    ! [B_8] : k4_subset_1('#skF_1',k4_xboole_0('#skF_1',B_8),'#skF_3') = k2_xboole_0(k4_xboole_0('#skF_1',B_8),'#skF_3') ),
    inference(resolution,[status(thm)],[c_37,c_1657])).

tff(c_15535,plain,(
    ! [B_346] : k4_subset_1('#skF_1',k4_xboole_0('#skF_1',B_346),'#skF_3') = k2_xboole_0('#skF_3',k4_xboole_0('#skF_1',B_346)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1709])).

tff(c_15582,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0('#skF_3',k4_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_15535])).

tff(c_15603,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_15582])).

tff(c_507,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_subset_1(A_67,B_68,C_69) = k4_xboole_0(B_68,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_534,plain,(
    ! [C_69] : k7_subset_1('#skF_1','#skF_2',C_69) = k4_xboole_0('#skF_2',C_69) ),
    inference(resolution,[status(thm)],[c_36,c_507])).

tff(c_32,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k7_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_588,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_32])).

tff(c_122896,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15603,c_588])).

tff(c_28,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_26,plain,(
    ! [A_29] : k3_xboole_0(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_79,plain,(
    ! [A_39] : k3_xboole_0(k1_xboole_0,A_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_26])).

tff(c_146,plain,(
    ! [A_41,B_42] : m1_subset_1(k4_xboole_0(A_41,B_42),k1_zfmisc_1(A_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8])).

tff(c_149,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_146])).

tff(c_632,plain,(
    ! [A_74,B_75,C_76] :
      ( k9_subset_1(A_74,B_75,C_76) = k3_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_941,plain,(
    ! [A_89,B_90] : k9_subset_1(A_89,B_90,A_89) = k3_xboole_0(B_90,A_89) ),
    inference(resolution,[status(thm)],[c_149,c_632])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] :
      ( m1_subset_1(k9_subset_1(A_12,B_13,C_14),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(C_14,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_947,plain,(
    ! [B_90,A_89] :
      ( m1_subset_1(k3_xboole_0(B_90,A_89),k1_zfmisc_1(A_89))
      | ~ m1_subset_1(A_89,k1_zfmisc_1(A_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_12])).

tff(c_955,plain,(
    ! [B_91,A_92] : m1_subset_1(k3_xboole_0(B_91,A_92),k1_zfmisc_1(A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_947])).

tff(c_983,plain,(
    ! [A_93] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_93)) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_955])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k3_subset_1(A_5,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_990,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = k3_subset_1(A_93,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_983,c_6])).

tff(c_997,plain,(
    ! [A_93] : k3_subset_1(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_990])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_subset_1(A_15,B_16)) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_998,plain,(
    ! [A_93] : k3_subset_1(A_93,k3_subset_1(A_93,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_983,c_14])).

tff(c_1252,plain,(
    ! [A_93] : k3_subset_1(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_998])).

tff(c_247,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_258,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_247])).

tff(c_292,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_277])).

tff(c_297,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_37])).

tff(c_318,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_297,c_6])).

tff(c_322,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_318])).

tff(c_151,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_28] : k2_xboole_0(A_28,k1_xboole_0) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_167,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_24])).

tff(c_290,plain,(
    ! [A_30] : k4_xboole_0(A_30,A_30) = k3_subset_1(A_30,A_30) ),
    inference(resolution,[status(thm)],[c_149,c_277])).

tff(c_1282,plain,(
    ! [A_104] : k4_xboole_0(A_104,A_104) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_290])).

tff(c_30,plain,(
    ! [A_31,B_32,C_33] : k2_xboole_0(k4_xboole_0(A_31,B_32),k3_xboole_0(A_31,C_33)) = k4_xboole_0(A_31,k4_xboole_0(B_32,C_33)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1287,plain,(
    ! [A_104,C_33] : k4_xboole_0(A_104,k4_xboole_0(A_104,C_33)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_104,C_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_30])).

tff(c_2848,plain,(
    ! [A_156,C_157] : k4_xboole_0(A_156,k4_xboole_0(A_156,C_157)) = k3_xboole_0(A_156,C_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_1287])).

tff(c_2947,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_2848])).

tff(c_2969,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_2947])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_1314,plain,(
    ! [A_104,C_33] : k4_xboole_0(A_104,k4_xboole_0(A_104,C_33)) = k3_xboole_0(A_104,C_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_1287])).

tff(c_291,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_37,c_277])).

tff(c_2847,plain,(
    ! [A_7,B_8] : k3_subset_1(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1314,c_291])).

tff(c_257,plain,(
    ! [A_7,B_8] : k3_subset_1(A_7,k3_subset_1(A_7,k4_xboole_0(A_7,B_8))) = k4_xboole_0(A_7,B_8) ),
    inference(resolution,[status(thm)],[c_37,c_247])).

tff(c_3702,plain,(
    ! [A_169,B_170] : k3_subset_1(A_169,k3_xboole_0(A_169,B_170)) = k4_xboole_0(A_169,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_257])).

tff(c_4335,plain,(
    ! [B_186,A_187] : k3_subset_1(B_186,k3_xboole_0(A_187,B_186)) = k4_xboole_0(B_186,A_187) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3702])).

tff(c_4359,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k3_subset_1('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2969,c_4335])).

tff(c_4384,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_4359])).

tff(c_4394,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k3_subset_1('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4384,c_2847])).

tff(c_4432,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_4394])).

tff(c_393,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k7_subset_1(A_59,B_60,C_61),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5031,plain,(
    ! [A_197,B_198,C_199] :
      ( k4_xboole_0(A_197,k7_subset_1(A_197,B_198,C_199)) = k3_subset_1(A_197,k7_subset_1(A_197,B_198,C_199))
      | ~ m1_subset_1(B_198,k1_zfmisc_1(A_197)) ) ),
    inference(resolution,[status(thm)],[c_393,c_6])).

tff(c_5095,plain,(
    ! [C_199] : k4_xboole_0('#skF_1',k7_subset_1('#skF_1','#skF_2',C_199)) = k3_subset_1('#skF_1',k7_subset_1('#skF_1','#skF_2',C_199)) ),
    inference(resolution,[status(thm)],[c_36,c_5031])).

tff(c_5132,plain,(
    ! [C_199] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_199)) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',C_199)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_534,c_5095])).

tff(c_820,plain,(
    ! [A_83,B_84,C_85] : k2_xboole_0(k4_xboole_0(A_83,B_84),k3_xboole_0(A_83,C_85)) = k4_xboole_0(A_83,k4_xboole_0(B_84,C_85)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2024,plain,(
    ! [A_130,C_131,B_132] : k2_xboole_0(k3_xboole_0(A_130,C_131),k4_xboole_0(A_130,B_132)) = k4_xboole_0(A_130,k4_xboole_0(B_132,C_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_2])).

tff(c_3304,plain,(
    ! [C_160] : k2_xboole_0(k3_xboole_0('#skF_1',C_160),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_160)) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_2024])).

tff(c_3348,plain,(
    ! [A_3] : k2_xboole_0(k3_xboole_0(A_3,'#skF_1'),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3304])).

tff(c_142433,plain,(
    ! [A_1207] : k2_xboole_0(k3_xboole_0(A_1207,'#skF_1'),k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',A_1207)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5132,c_3348])).

tff(c_142519,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_142433])).

tff(c_142572,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122896,c_142519])).

%------------------------------------------------------------------------------
