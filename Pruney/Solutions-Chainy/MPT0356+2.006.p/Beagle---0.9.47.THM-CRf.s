%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:56 EST 2020

% Result     : Theorem 11.21s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 404 expanded)
%              Number of leaves         :   40 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          :  147 ( 766 expanded)
%              Number of equality atoms :   47 ( 170 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_122,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_102,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r2_xboole_0(A,B)
          & A != B
          & ~ r2_xboole_0(B,A) )
    <=> r3_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k5_xboole_0(B,C))
    <=> ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_92,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(c_66,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_68,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_438,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_450,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_438])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [A_45] : ~ v1_xboole_0(k1_zfmisc_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_197,plain,(
    ! [B_82,A_83] :
      ( r2_hidden(B_82,A_83)
      | ~ m1_subset_1(B_82,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_52,plain,(
    ! [A_40] : k3_tarski(k1_zfmisc_1(A_40)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_133,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,k3_tarski(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_139,plain,(
    ! [A_68,A_40] :
      ( r1_tarski(A_68,A_40)
      | ~ r2_hidden(A_68,k1_zfmisc_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_133])).

tff(c_204,plain,(
    ! [B_82,A_40] :
      ( r1_tarski(B_82,A_40)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_40))
      | v1_xboole_0(k1_zfmisc_1(A_40)) ) ),
    inference(resolution,[status(thm)],[c_197,c_139])).

tff(c_210,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_204])).

tff(c_222,plain,(
    r1_tarski('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_210])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_230,plain,(
    k3_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_222,c_36])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_231,plain,(
    k2_xboole_0('#skF_4','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_222,c_28])).

tff(c_1010,plain,(
    ! [A_140,B_141] : k5_xboole_0(k5_xboole_0(A_140,B_141),k2_xboole_0(A_140,B_141)) = k3_xboole_0(A_140,B_141) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1061,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_2'),'#skF_2') = k3_xboole_0('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1010])).

tff(c_1092,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_2'),'#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_1061])).

tff(c_1146,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_4','#skF_2')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1092])).

tff(c_18,plain,(
    ! [B_10] : r3_xboole_0(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_290,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(B_89,A_90)
      | r1_tarski(A_90,B_89)
      | ~ r3_xboole_0(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(resolution,[status(thm)],[c_18,c_290])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,'#skF_1'(A_16,B_17,C_18))
      | k2_xboole_0(A_16,C_18) = B_17
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2084,plain,(
    ! [B_178,A_179,C_180] :
      ( ~ r1_tarski(B_178,'#skF_1'(A_179,B_178,C_180))
      | k2_xboole_0(A_179,C_180) = B_178
      | ~ r1_tarski(C_180,B_178)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2092,plain,(
    ! [B_17,C_18] :
      ( k2_xboole_0(B_17,C_18) = B_17
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(B_17,B_17) ) ),
    inference(resolution,[status(thm)],[c_34,c_2084])).

tff(c_2099,plain,(
    ! [B_181,C_182] :
      ( k2_xboole_0(B_181,C_182) = B_181
      | ~ r1_tarski(C_182,B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_2092])).

tff(c_2197,plain,(
    k2_xboole_0('#skF_2','#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_222,c_2099])).

tff(c_48,plain,(
    ! [A_36,B_37] : k5_xboole_0(k5_xboole_0(A_36,B_37),k2_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2248,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_4'),'#skF_2') = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2197,c_48])).

tff(c_2269,plain,(
    k3_xboole_0('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_2,c_2,c_2248])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2377,plain,(
    k5_xboole_0('#skF_2','#skF_4') = k4_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_12])).

tff(c_2384,plain,(
    k5_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_2377])).

tff(c_2819,plain,(
    k5_xboole_0('#skF_4','#skF_2') = k3_subset_1('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_2])).

tff(c_556,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_xboole_0(A_113,k3_xboole_0(B_114,C_115))
      | ~ r1_tarski(A_113,k5_xboole_0(B_114,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_572,plain,(
    ! [A_113] :
      ( r1_xboole_0(A_113,'#skF_4')
      | ~ r1_tarski(A_113,k5_xboole_0('#skF_4','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_556])).

tff(c_4581,plain,(
    ! [A_203] :
      ( r1_xboole_0(A_203,'#skF_4')
      | ~ r1_tarski(A_203,k3_subset_1('#skF_2','#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2819,c_572])).

tff(c_4599,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_4581])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4605,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_4599,c_4])).

tff(c_72,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_451,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_438])).

tff(c_223,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_238,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_223,c_36])).

tff(c_239,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_223,c_28])).

tff(c_1064,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_2'),'#skF_2') = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_1010])).

tff(c_1093,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_2'),'#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_1064])).

tff(c_1202,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1093])).

tff(c_2196,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_223,c_2099])).

tff(c_2210,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2196,c_48])).

tff(c_2231,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_2,c_2,c_2210])).

tff(c_2347,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2231,c_12])).

tff(c_2354,plain,(
    k5_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_2347])).

tff(c_1246,plain,(
    ! [A_144,B_145,C_146] : k2_xboole_0(k2_xboole_0(A_144,B_145),C_146) = k2_xboole_0(A_144,k2_xboole_0(B_145,C_146)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7975,plain,(
    ! [C_269] : k2_xboole_0('#skF_4',k2_xboole_0('#skF_2',C_269)) = k2_xboole_0('#skF_2',C_269) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_1246])).

tff(c_44,plain,(
    ! [A_31,B_32] : r1_tarski(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8042,plain,(
    ! [C_269] : r1_tarski('#skF_4',k2_xboole_0('#skF_2',C_269)) ),
    inference(superposition,[status(thm),theory(equality)],[c_7975,c_44])).

tff(c_42,plain,(
    ! [C_30,A_28,B_29] :
      ( r1_xboole_0(k3_xboole_0(C_30,A_28),k3_xboole_0(C_30,B_29))
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1760,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_tarski(A_159,k5_xboole_0(B_160,C_161))
      | ~ r1_xboole_0(A_159,k3_xboole_0(B_160,C_161))
      | ~ r1_tarski(A_159,k2_xboole_0(B_160,C_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15322,plain,(
    ! [C_417,A_418,B_419] :
      ( r1_tarski(k3_xboole_0(C_417,A_418),k5_xboole_0(C_417,B_419))
      | ~ r1_tarski(k3_xboole_0(C_417,A_418),k2_xboole_0(C_417,B_419))
      | ~ r1_xboole_0(A_418,B_419) ) ),
    inference(resolution,[status(thm)],[c_42,c_1760])).

tff(c_15455,plain,(
    ! [B_419] :
      ( r1_tarski('#skF_4',k5_xboole_0('#skF_2',B_419))
      | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_4'),k2_xboole_0('#skF_2',B_419))
      | ~ r1_xboole_0('#skF_4',B_419) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2269,c_15322])).

tff(c_15902,plain,(
    ! [B_424] :
      ( r1_tarski('#skF_4',k5_xboole_0('#skF_2',B_424))
      | ~ r1_xboole_0('#skF_4',B_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8042,c_2269,c_15455])).

tff(c_15957,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2354,c_15902])).

tff(c_15991,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4605,c_15957])).

tff(c_15993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_15991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:03:55 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.21/4.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.38  
% 11.21/4.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.38  %$ r3_xboole_0 > r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 11.21/4.38  
% 11.21/4.38  %Foreground sorts:
% 11.21/4.38  
% 11.21/4.38  
% 11.21/4.38  %Background operators:
% 11.21/4.38  
% 11.21/4.38  
% 11.21/4.38  %Foreground operators:
% 11.21/4.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.21/4.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.21/4.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.21/4.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.21/4.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.21/4.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.21/4.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.21/4.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.21/4.38  tff('#skF_2', type, '#skF_2': $i).
% 11.21/4.38  tff('#skF_3', type, '#skF_3': $i).
% 11.21/4.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.21/4.38  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 11.21/4.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.21/4.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.21/4.38  tff('#skF_4', type, '#skF_4': $i).
% 11.21/4.38  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 11.21/4.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.21/4.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.21/4.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.21/4.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.21/4.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.21/4.38  
% 11.21/4.40  tff(f_132, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 11.21/4.40  tff(f_119, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.21/4.40  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 11.21/4.40  tff(f_122, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.21/4.40  tff(f_115, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.21/4.40  tff(f_102, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 11.21/4.40  tff(f_100, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_zfmisc_1)).
% 11.21/4.40  tff(f_78, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.21/4.40  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 11.21/4.40  tff(f_96, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 11.21/4.40  tff(f_51, axiom, (![A, B]: (~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)) <=> r3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_xboole_1)).
% 11.21/4.40  tff(f_37, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_xboole_0)).
% 11.21/4.40  tff(f_74, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 11.21/4.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 11.21/4.40  tff(f_57, axiom, (![A, B, C]: (r1_tarski(A, k5_xboole_0(B, C)) <=> (r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, k3_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_xboole_1)).
% 11.21/4.40  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 11.21/4.40  tff(f_80, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 11.21/4.40  tff(f_92, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.21/4.40  tff(f_90, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 11.21/4.40  tff(c_66, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.21/4.40  tff(c_68, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.21/4.40  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.21/4.40  tff(c_438, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 11.21/4.40  tff(c_450, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_438])).
% 11.21/4.40  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.21/4.40  tff(c_64, plain, (![A_45]: (~v1_xboole_0(k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.21/4.40  tff(c_197, plain, (![B_82, A_83]: (r2_hidden(B_82, A_83) | ~m1_subset_1(B_82, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.40  tff(c_52, plain, (![A_40]: (k3_tarski(k1_zfmisc_1(A_40))=A_40)), inference(cnfTransformation, [status(thm)], [f_102])).
% 11.21/4.40  tff(c_133, plain, (![A_68, B_69]: (r1_tarski(A_68, k3_tarski(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.21/4.40  tff(c_139, plain, (![A_68, A_40]: (r1_tarski(A_68, A_40) | ~r2_hidden(A_68, k1_zfmisc_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_133])).
% 11.21/4.40  tff(c_204, plain, (![B_82, A_40]: (r1_tarski(B_82, A_40) | ~m1_subset_1(B_82, k1_zfmisc_1(A_40)) | v1_xboole_0(k1_zfmisc_1(A_40)))), inference(resolution, [status(thm)], [c_197, c_139])).
% 11.21/4.40  tff(c_210, plain, (![B_87, A_88]: (r1_tarski(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_64, c_204])).
% 11.21/4.40  tff(c_222, plain, (r1_tarski('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_210])).
% 11.21/4.40  tff(c_36, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.21/4.40  tff(c_230, plain, (k3_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_222, c_36])).
% 11.21/4.40  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.21/4.40  tff(c_231, plain, (k2_xboole_0('#skF_4', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_222, c_28])).
% 11.21/4.40  tff(c_1010, plain, (![A_140, B_141]: (k5_xboole_0(k5_xboole_0(A_140, B_141), k2_xboole_0(A_140, B_141))=k3_xboole_0(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.21/4.40  tff(c_1061, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_1010])).
% 11.21/4.40  tff(c_1092, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_2'), '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_230, c_1061])).
% 11.21/4.40  tff(c_1146, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_4', '#skF_2'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2, c_1092])).
% 11.21/4.40  tff(c_18, plain, (![B_10]: (r3_xboole_0(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.21/4.40  tff(c_290, plain, (![B_89, A_90]: (r1_tarski(B_89, A_90) | r1_tarski(A_90, B_89) | ~r3_xboole_0(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.21/4.40  tff(c_310, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(resolution, [status(thm)], [c_18, c_290])).
% 11.21/4.40  tff(c_34, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, '#skF_1'(A_16, B_17, C_18)) | k2_xboole_0(A_16, C_18)=B_17 | ~r1_tarski(C_18, B_17) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.21/4.40  tff(c_2084, plain, (![B_178, A_179, C_180]: (~r1_tarski(B_178, '#skF_1'(A_179, B_178, C_180)) | k2_xboole_0(A_179, C_180)=B_178 | ~r1_tarski(C_180, B_178) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_74])).
% 11.21/4.40  tff(c_2092, plain, (![B_17, C_18]: (k2_xboole_0(B_17, C_18)=B_17 | ~r1_tarski(C_18, B_17) | ~r1_tarski(B_17, B_17))), inference(resolution, [status(thm)], [c_34, c_2084])).
% 11.21/4.40  tff(c_2099, plain, (![B_181, C_182]: (k2_xboole_0(B_181, C_182)=B_181 | ~r1_tarski(C_182, B_181))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_2092])).
% 11.21/4.40  tff(c_2197, plain, (k2_xboole_0('#skF_2', '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_222, c_2099])).
% 11.21/4.40  tff(c_48, plain, (![A_36, B_37]: (k5_xboole_0(k5_xboole_0(A_36, B_37), k2_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_96])).
% 11.21/4.40  tff(c_2248, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_4'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2197, c_48])).
% 11.21/4.40  tff(c_2269, plain, (k3_xboole_0('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_2, c_2, c_2248])).
% 11.21/4.40  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.40  tff(c_2377, plain, (k5_xboole_0('#skF_2', '#skF_4')=k4_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2269, c_12])).
% 11.21/4.40  tff(c_2384, plain, (k5_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_450, c_2377])).
% 11.21/4.40  tff(c_2819, plain, (k5_xboole_0('#skF_4', '#skF_2')=k3_subset_1('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2384, c_2])).
% 11.21/4.40  tff(c_556, plain, (![A_113, B_114, C_115]: (r1_xboole_0(A_113, k3_xboole_0(B_114, C_115)) | ~r1_tarski(A_113, k5_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.40  tff(c_572, plain, (![A_113]: (r1_xboole_0(A_113, '#skF_4') | ~r1_tarski(A_113, k5_xboole_0('#skF_4', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_230, c_556])).
% 11.21/4.40  tff(c_4581, plain, (![A_203]: (r1_xboole_0(A_203, '#skF_4') | ~r1_tarski(A_203, k3_subset_1('#skF_2', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2819, c_572])).
% 11.21/4.40  tff(c_4599, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_68, c_4581])).
% 11.21/4.40  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.40  tff(c_4605, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_4599, c_4])).
% 11.21/4.40  tff(c_72, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 11.21/4.40  tff(c_451, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_438])).
% 11.21/4.40  tff(c_223, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_210])).
% 11.21/4.40  tff(c_238, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_223, c_36])).
% 11.21/4.40  tff(c_239, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_223, c_28])).
% 11.21/4.40  tff(c_1064, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_239, c_1010])).
% 11.21/4.40  tff(c_1093, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_2'), '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_238, c_1064])).
% 11.21/4.40  tff(c_1202, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_1093])).
% 11.21/4.40  tff(c_2196, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_223, c_2099])).
% 11.21/4.40  tff(c_2210, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2196, c_48])).
% 11.21/4.40  tff(c_2231, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_2, c_2, c_2210])).
% 11.21/4.40  tff(c_2347, plain, (k5_xboole_0('#skF_2', '#skF_3')=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2231, c_12])).
% 11.21/4.40  tff(c_2354, plain, (k5_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_2347])).
% 11.21/4.40  tff(c_1246, plain, (![A_144, B_145, C_146]: (k2_xboole_0(k2_xboole_0(A_144, B_145), C_146)=k2_xboole_0(A_144, k2_xboole_0(B_145, C_146)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 11.21/4.40  tff(c_7975, plain, (![C_269]: (k2_xboole_0('#skF_4', k2_xboole_0('#skF_2', C_269))=k2_xboole_0('#skF_2', C_269))), inference(superposition, [status(thm), theory('equality')], [c_231, c_1246])).
% 11.21/4.40  tff(c_44, plain, (![A_31, B_32]: (r1_tarski(A_31, k2_xboole_0(A_31, B_32)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 11.21/4.40  tff(c_8042, plain, (![C_269]: (r1_tarski('#skF_4', k2_xboole_0('#skF_2', C_269)))), inference(superposition, [status(thm), theory('equality')], [c_7975, c_44])).
% 11.21/4.40  tff(c_42, plain, (![C_30, A_28, B_29]: (r1_xboole_0(k3_xboole_0(C_30, A_28), k3_xboole_0(C_30, B_29)) | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.40  tff(c_1760, plain, (![A_159, B_160, C_161]: (r1_tarski(A_159, k5_xboole_0(B_160, C_161)) | ~r1_xboole_0(A_159, k3_xboole_0(B_160, C_161)) | ~r1_tarski(A_159, k2_xboole_0(B_160, C_161)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.40  tff(c_15322, plain, (![C_417, A_418, B_419]: (r1_tarski(k3_xboole_0(C_417, A_418), k5_xboole_0(C_417, B_419)) | ~r1_tarski(k3_xboole_0(C_417, A_418), k2_xboole_0(C_417, B_419)) | ~r1_xboole_0(A_418, B_419))), inference(resolution, [status(thm)], [c_42, c_1760])).
% 11.21/4.40  tff(c_15455, plain, (![B_419]: (r1_tarski('#skF_4', k5_xboole_0('#skF_2', B_419)) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_4'), k2_xboole_0('#skF_2', B_419)) | ~r1_xboole_0('#skF_4', B_419))), inference(superposition, [status(thm), theory('equality')], [c_2269, c_15322])).
% 11.21/4.40  tff(c_15902, plain, (![B_424]: (r1_tarski('#skF_4', k5_xboole_0('#skF_2', B_424)) | ~r1_xboole_0('#skF_4', B_424))), inference(demodulation, [status(thm), theory('equality')], [c_8042, c_2269, c_15455])).
% 11.21/4.40  tff(c_15957, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2354, c_15902])).
% 11.21/4.40  tff(c_15991, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4605, c_15957])).
% 11.21/4.40  tff(c_15993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_15991])).
% 11.21/4.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.40  
% 11.21/4.40  Inference rules
% 11.21/4.40  ----------------------
% 11.21/4.40  #Ref     : 0
% 11.21/4.40  #Sup     : 4239
% 11.21/4.40  #Fact    : 4
% 11.21/4.40  #Define  : 0
% 11.21/4.40  #Split   : 21
% 11.21/4.40  #Chain   : 0
% 11.21/4.40  #Close   : 0
% 11.21/4.40  
% 11.21/4.40  Ordering : KBO
% 11.21/4.40  
% 11.21/4.40  Simplification rules
% 11.21/4.40  ----------------------
% 11.21/4.40  #Subsume      : 628
% 11.21/4.40  #Demod        : 3223
% 11.21/4.40  #Tautology    : 1269
% 11.21/4.40  #SimpNegUnit  : 102
% 11.21/4.40  #BackRed      : 22
% 11.21/4.40  
% 11.21/4.40  #Partial instantiations: 0
% 11.21/4.40  #Strategies tried      : 1
% 11.21/4.40  
% 11.21/4.40  Timing (in seconds)
% 11.21/4.40  ----------------------
% 11.21/4.40  Preprocessing        : 0.35
% 11.21/4.40  Parsing              : 0.19
% 11.21/4.41  CNF conversion       : 0.02
% 11.21/4.41  Main loop            : 3.27
% 11.21/4.41  Inferencing          : 0.71
% 11.21/4.41  Reduction            : 1.58
% 11.21/4.41  Demodulation         : 1.28
% 11.21/4.41  BG Simplification    : 0.08
% 11.21/4.41  Subsumption          : 0.72
% 11.21/4.41  Abstraction          : 0.10
% 11.21/4.41  MUC search           : 0.00
% 11.21/4.41  Cooper               : 0.00
% 11.21/4.41  Total                : 3.66
% 11.21/4.41  Index Insertion      : 0.00
% 11.21/4.41  Index Deletion       : 0.00
% 11.21/4.41  Index Matching       : 0.00
% 11.21/4.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
