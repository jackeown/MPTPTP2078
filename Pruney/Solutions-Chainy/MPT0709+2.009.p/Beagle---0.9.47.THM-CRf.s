%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:25 EST 2020

% Result     : Theorem 12.55s
% Output     : CNFRefutation 12.73s
% Verified   : 
% Statistics : Number of formulae       :  129 (1763 expanded)
%              Number of leaves         :   42 ( 640 expanded)
%              Depth                    :   33
%              Number of atoms          :  245 (3336 expanded)
%              Number of equality atoms :   69 (1328 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( ( r1_tarski(A,k1_relat_1(B))
            & v2_funct_1(B) )
         => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_127,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
          & r1_tarski(A,k1_relat_1(C))
          & v2_funct_1(C) )
       => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(c_52,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_54,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    ! [A_28] :
      ( v1_relat_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [A_57,B_58] :
      ( k2_xboole_0(A_57,B_58) = B_58
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_186,plain,(
    ! [A_7] : k2_xboole_0(k1_xboole_0,A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_12,c_170])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_264,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_79,plain,(
    ! [A_48] :
      ( k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_92,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_319,plain,(
    ! [B_73] : k3_xboole_0(k1_xboole_0,B_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_92])).

tff(c_337,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_16,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_296,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_264])).

tff(c_461,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_296])).

tff(c_24,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [C_31,A_29,B_30] :
      ( k6_subset_1(k10_relat_1(C_31,A_29),k10_relat_1(C_31,B_30)) = k10_relat_1(C_31,k6_subset_1(A_29,B_30))
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_991,plain,(
    ! [C_115,A_116,B_117] :
      ( k4_xboole_0(k10_relat_1(C_115,A_116),k10_relat_1(C_115,B_117)) = k10_relat_1(C_115,k4_xboole_0(A_116,B_117))
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_40])).

tff(c_1001,plain,(
    ! [C_115,B_117] :
      ( k10_relat_1(C_115,k4_xboole_0(B_117,B_117)) = k1_xboole_0
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_461])).

tff(c_1034,plain,(
    ! [C_118] :
      ( k10_relat_1(C_118,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_1001])).

tff(c_1040,plain,
    ( k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1034])).

tff(c_1044,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1040])).

tff(c_30,plain,(
    ! [A_22] :
      ( k10_relat_1(A_22,k2_relat_1(A_22)) = k1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_753,plain,(
    ! [C_101,A_102,B_103] :
      ( k2_xboole_0(k10_relat_1(C_101,A_102),k10_relat_1(C_101,B_103)) = k10_relat_1(C_101,k2_xboole_0(A_102,B_103))
      | ~ v1_relat_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2773,plain,(
    ! [A_158,A_159] :
      ( k2_xboole_0(k10_relat_1(A_158,A_159),k1_relat_1(A_158)) = k10_relat_1(A_158,k2_xboole_0(A_159,k2_relat_1(A_158)))
      | ~ v1_relat_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_753])).

tff(c_2806,plain,
    ( k10_relat_1('#skF_2',k2_xboole_0(k1_xboole_0,k2_relat_1('#skF_2'))) = k2_xboole_0(k1_xboole_0,k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_2773])).

tff(c_2831,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_60,c_186,c_186,c_2806])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_863,plain,(
    ! [B_108,A_109] :
      ( k9_relat_1(B_108,k10_relat_1(B_108,A_109)) = A_109
      | ~ r1_tarski(A_109,k2_relat_1(B_108))
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_882,plain,(
    ! [B_108] :
      ( k9_relat_1(B_108,k10_relat_1(B_108,k2_relat_1(B_108))) = k2_relat_1(B_108)
      | ~ v1_funct_1(B_108)
      | ~ v1_relat_1(B_108) ) ),
    inference(resolution,[status(thm)],[c_8,c_863])).

tff(c_2861,plain,
    ( k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_882])).

tff(c_2915,plain,(
    k9_relat_1('#skF_2',k1_relat_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_2861])).

tff(c_603,plain,(
    ! [B_89,A_90] :
      ( k10_relat_1(k2_funct_1(B_89),A_90) = k9_relat_1(B_89,A_90)
      | ~ v2_funct_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_28,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k10_relat_1(B_21,A_20),k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3257,plain,(
    ! [B_163,A_164] :
      ( r1_tarski(k9_relat_1(B_163,A_164),k1_relat_1(k2_funct_1(B_163)))
      | ~ v1_relat_1(k2_funct_1(B_163))
      | ~ v2_funct_1(B_163)
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_28])).

tff(c_3265,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2915,c_3257])).

tff(c_3284,plain,
    ( r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_3265])).

tff(c_3289,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3284])).

tff(c_3292,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_3289])).

tff(c_3296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3292])).

tff(c_3298,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3284])).

tff(c_36,plain,(
    ! [A_28] :
      ( v1_funct_1(k2_funct_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1031,plain,(
    ! [C_115] :
      ( k10_relat_1(C_115,k1_xboole_0) = k1_xboole_0
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_1001])).

tff(c_3403,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3298,c_1031])).

tff(c_3411,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3403])).

tff(c_3414,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_3411])).

tff(c_3418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_3414])).

tff(c_3419,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3403])).

tff(c_46,plain,(
    ! [B_37,A_36] :
      ( k10_relat_1(k2_funct_1(B_37),A_36) = k9_relat_1(B_37,A_36)
      | ~ v2_funct_1(B_37)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10056,plain,(
    ! [B_242,A_243,A_244] :
      ( k2_xboole_0(k10_relat_1(k2_funct_1(B_242),A_243),k9_relat_1(B_242,A_244)) = k10_relat_1(k2_funct_1(B_242),k2_xboole_0(A_243,A_244))
      | ~ v1_relat_1(k2_funct_1(B_242))
      | ~ v2_funct_1(B_242)
      | ~ v1_funct_1(B_242)
      | ~ v1_relat_1(B_242) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_753])).

tff(c_10083,plain,(
    ! [A_244] :
      ( k10_relat_1(k2_funct_1('#skF_2'),k2_xboole_0(k1_xboole_0,A_244)) = k2_xboole_0(k1_xboole_0,k9_relat_1('#skF_2',A_244))
      | ~ v1_relat_1(k2_funct_1('#skF_2'))
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3419,c_10056])).

tff(c_10127,plain,(
    ! [A_244] : k10_relat_1(k2_funct_1('#skF_2'),A_244) = k9_relat_1('#skF_2',A_244) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_3298,c_186,c_186,c_10083])).

tff(c_3420,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3403])).

tff(c_775,plain,(
    ! [A_22,A_102] :
      ( k2_xboole_0(k10_relat_1(A_22,A_102),k1_relat_1(A_22)) = k10_relat_1(A_22,k2_xboole_0(A_102,k2_relat_1(A_22)))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_753])).

tff(c_3500,plain,
    ( k10_relat_1(k2_funct_1('#skF_2'),k2_xboole_0(k1_xboole_0,k2_relat_1(k2_funct_1('#skF_2')))) = k2_xboole_0(k1_xboole_0,k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3419,c_775])).

tff(c_3557,plain,(
    k10_relat_1(k2_funct_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) = k1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_3298,c_186,c_186,c_3500])).

tff(c_3766,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3557,c_882])).

tff(c_3825,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_3420,c_3766])).

tff(c_48,plain,(
    ! [B_39,A_38] :
      ( k9_relat_1(k2_funct_1(B_39),A_38) = k10_relat_1(B_39,A_38)
      | ~ v2_funct_1(B_39)
      | ~ v1_funct_1(B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4263,plain,
    ( k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3825,c_48])).

tff(c_4286,plain,(
    k10_relat_1('#skF_2',k1_relat_1(k2_funct_1('#skF_2'))) = k2_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_4263])).

tff(c_32,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k10_relat_1(B_24,A_23),k10_relat_1(B_24,k2_relat_1(B_24)))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2888,plain,(
    ! [A_23] :
      ( r1_tarski(k10_relat_1('#skF_2',A_23),k1_relat_1('#skF_2'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_32])).

tff(c_2932,plain,(
    ! [A_23] : r1_tarski(k10_relat_1('#skF_2',A_23),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2888])).

tff(c_4300,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_2932])).

tff(c_3297,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3284])).

tff(c_627,plain,(
    ! [B_89] :
      ( k9_relat_1(B_89,k2_relat_1(k2_funct_1(B_89))) = k1_relat_1(k2_funct_1(B_89))
      | ~ v2_funct_1(B_89)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(k2_funct_1(B_89)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_603])).

tff(c_50,plain,(
    ! [A_40,B_41,C_42] :
      ( r1_tarski(A_40,B_41)
      | ~ v2_funct_1(C_42)
      | ~ r1_tarski(A_40,k1_relat_1(C_42))
      | ~ r1_tarski(k9_relat_1(C_42,A_40),k9_relat_1(C_42,B_41))
      | ~ v1_funct_1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2954,plain,(
    ! [B_41] :
      ( r1_tarski(k1_relat_1('#skF_2'),B_41)
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
      | ~ r1_tarski(k2_relat_1('#skF_2'),k9_relat_1('#skF_2',B_41))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2915,c_50])).

tff(c_4606,plain,(
    ! [B_178] :
      ( r1_tarski(k1_relat_1('#skF_2'),B_178)
      | ~ r1_tarski(k2_relat_1('#skF_2'),k9_relat_1('#skF_2',B_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_8,c_54,c_2954])).

tff(c_4610,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2')))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_627,c_4606])).

tff(c_4637,plain,(
    r1_tarski(k1_relat_1('#skF_2'),k2_relat_1(k2_funct_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_60,c_58,c_54,c_3297,c_4610])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4653,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4637,c_4])).

tff(c_4662,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4300,c_4653])).

tff(c_44,plain,(
    ! [B_35,A_34] :
      ( k9_relat_1(B_35,k10_relat_1(B_35,A_34)) = A_34
      | ~ r1_tarski(A_34,k2_relat_1(B_35))
      | ~ v1_funct_1(B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4702,plain,(
    ! [A_34] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_34)) = A_34
      | ~ r1_tarski(A_34,k1_relat_1('#skF_2'))
      | ~ v1_funct_1(k2_funct_1('#skF_2'))
      | ~ v1_relat_1(k2_funct_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4662,c_44])).

tff(c_4724,plain,(
    ! [A_34] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k10_relat_1(k2_funct_1('#skF_2'),A_34)) = A_34
      | ~ r1_tarski(A_34,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3298,c_3420,c_4702])).

tff(c_26847,plain,(
    ! [A_405] :
      ( k9_relat_1(k2_funct_1('#skF_2'),k9_relat_1('#skF_2',A_405)) = A_405
      | ~ r1_tarski(A_405,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10127,c_4724])).

tff(c_26901,plain,(
    ! [A_405] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_405)) = A_405
      | ~ v2_funct_1('#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski(A_405,k1_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26847,c_48])).

tff(c_27357,plain,(
    ! [A_408] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_408)) = A_408
      | ~ r1_tarski(A_408,k1_relat_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_26901])).

tff(c_27388,plain,(
    k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_27357])).

tff(c_27416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_27388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.55/5.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.55/5.73  
% 12.55/5.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.55/5.73  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 12.55/5.73  
% 12.55/5.73  %Foreground sorts:
% 12.55/5.73  
% 12.55/5.73  
% 12.55/5.73  %Background operators:
% 12.55/5.73  
% 12.55/5.73  
% 12.55/5.73  %Foreground operators:
% 12.55/5.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.55/5.73  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.55/5.73  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.55/5.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.55/5.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.55/5.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.55/5.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.55/5.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.55/5.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.55/5.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.55/5.73  tff('#skF_2', type, '#skF_2': $i).
% 12.55/5.73  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.55/5.73  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.55/5.73  tff('#skF_1', type, '#skF_1': $i).
% 12.55/5.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.55/5.73  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.55/5.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.55/5.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.55/5.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.55/5.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.55/5.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.55/5.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.55/5.73  
% 12.73/5.75  tff(f_138, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 12.73/5.75  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.73/5.75  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 12.73/5.75  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.73/5.75  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.73/5.75  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.73/5.75  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.73/5.75  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 12.73/5.75  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.73/5.75  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.73/5.75  tff(f_85, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_funct_1)).
% 12.73/5.75  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 12.73/5.75  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 12.73/5.75  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.73/5.75  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 12.73/5.75  tff(f_107, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 12.73/5.75  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 12.73/5.75  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_1)).
% 12.73/5.75  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 12.73/5.75  tff(f_127, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 12.73/5.75  tff(c_52, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.73/5.75  tff(c_56, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.73/5.75  tff(c_60, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.73/5.75  tff(c_58, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.73/5.75  tff(c_54, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 12.73/5.75  tff(c_38, plain, (![A_28]: (v1_relat_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.75  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.73/5.75  tff(c_170, plain, (![A_57, B_58]: (k2_xboole_0(A_57, B_58)=B_58 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.73/5.75  tff(c_186, plain, (![A_7]: (k2_xboole_0(k1_xboole_0, A_7)=A_7)), inference(resolution, [status(thm)], [c_12, c_170])).
% 12.73/5.75  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.73/5.75  tff(c_264, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.73/5.75  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.73/5.75  tff(c_79, plain, (![A_48]: (k1_xboole_0=A_48 | ~r1_tarski(A_48, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/5.75  tff(c_92, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_79])).
% 12.73/5.75  tff(c_319, plain, (![B_73]: (k3_xboole_0(k1_xboole_0, B_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_264, c_92])).
% 12.73/5.75  tff(c_337, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_319])).
% 12.73/5.75  tff(c_16, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.73/5.75  tff(c_296, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_264])).
% 12.73/5.75  tff(c_461, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_296])).
% 12.73/5.75  tff(c_24, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.73/5.75  tff(c_40, plain, (![C_31, A_29, B_30]: (k6_subset_1(k10_relat_1(C_31, A_29), k10_relat_1(C_31, B_30))=k10_relat_1(C_31, k6_subset_1(A_29, B_30)) | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.73/5.75  tff(c_991, plain, (![C_115, A_116, B_117]: (k4_xboole_0(k10_relat_1(C_115, A_116), k10_relat_1(C_115, B_117))=k10_relat_1(C_115, k4_xboole_0(A_116, B_117)) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_40])).
% 12.73/5.75  tff(c_1001, plain, (![C_115, B_117]: (k10_relat_1(C_115, k4_xboole_0(B_117, B_117))=k1_xboole_0 | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(superposition, [status(thm), theory('equality')], [c_991, c_461])).
% 12.73/5.75  tff(c_1034, plain, (![C_118]: (k10_relat_1(C_118, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_118) | ~v1_relat_1(C_118))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_1001])).
% 12.73/5.75  tff(c_1040, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_60, c_1034])).
% 12.73/5.75  tff(c_1044, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1040])).
% 12.73/5.75  tff(c_30, plain, (![A_22]: (k10_relat_1(A_22, k2_relat_1(A_22))=k1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 12.73/5.75  tff(c_753, plain, (![C_101, A_102, B_103]: (k2_xboole_0(k10_relat_1(C_101, A_102), k10_relat_1(C_101, B_103))=k10_relat_1(C_101, k2_xboole_0(A_102, B_103)) | ~v1_relat_1(C_101))), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.73/5.75  tff(c_2773, plain, (![A_158, A_159]: (k2_xboole_0(k10_relat_1(A_158, A_159), k1_relat_1(A_158))=k10_relat_1(A_158, k2_xboole_0(A_159, k2_relat_1(A_158))) | ~v1_relat_1(A_158) | ~v1_relat_1(A_158))), inference(superposition, [status(thm), theory('equality')], [c_30, c_753])).
% 12.73/5.75  tff(c_2806, plain, (k10_relat_1('#skF_2', k2_xboole_0(k1_xboole_0, k2_relat_1('#skF_2')))=k2_xboole_0(k1_xboole_0, k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1044, c_2773])).
% 12.73/5.75  tff(c_2831, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_60, c_186, c_186, c_2806])).
% 12.73/5.75  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/5.75  tff(c_863, plain, (![B_108, A_109]: (k9_relat_1(B_108, k10_relat_1(B_108, A_109))=A_109 | ~r1_tarski(A_109, k2_relat_1(B_108)) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.73/5.75  tff(c_882, plain, (![B_108]: (k9_relat_1(B_108, k10_relat_1(B_108, k2_relat_1(B_108)))=k2_relat_1(B_108) | ~v1_funct_1(B_108) | ~v1_relat_1(B_108))), inference(resolution, [status(thm)], [c_8, c_863])).
% 12.73/5.75  tff(c_2861, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2831, c_882])).
% 12.73/5.75  tff(c_2915, plain, (k9_relat_1('#skF_2', k1_relat_1('#skF_2'))=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_2861])).
% 12.73/5.75  tff(c_603, plain, (![B_89, A_90]: (k10_relat_1(k2_funct_1(B_89), A_90)=k9_relat_1(B_89, A_90) | ~v2_funct_1(B_89) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.73/5.75  tff(c_28, plain, (![B_21, A_20]: (r1_tarski(k10_relat_1(B_21, A_20), k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.73/5.75  tff(c_3257, plain, (![B_163, A_164]: (r1_tarski(k9_relat_1(B_163, A_164), k1_relat_1(k2_funct_1(B_163))) | ~v1_relat_1(k2_funct_1(B_163)) | ~v2_funct_1(B_163) | ~v1_funct_1(B_163) | ~v1_relat_1(B_163))), inference(superposition, [status(thm), theory('equality')], [c_603, c_28])).
% 12.73/5.75  tff(c_3265, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2915, c_3257])).
% 12.73/5.75  tff(c_3284, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_3265])).
% 12.73/5.75  tff(c_3289, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3284])).
% 12.73/5.75  tff(c_3292, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_3289])).
% 12.73/5.75  tff(c_3296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3292])).
% 12.73/5.75  tff(c_3298, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3284])).
% 12.73/5.75  tff(c_36, plain, (![A_28]: (v1_funct_1(k2_funct_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.73/5.75  tff(c_1031, plain, (![C_115]: (k10_relat_1(C_115, k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_461, c_1001])).
% 12.73/5.75  tff(c_3403, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0 | ~v1_funct_1(k2_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_3298, c_1031])).
% 12.73/5.75  tff(c_3411, plain, (~v1_funct_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_3403])).
% 12.73/5.75  tff(c_3414, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_3411])).
% 12.73/5.75  tff(c_3418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_3414])).
% 12.73/5.75  tff(c_3419, plain, (k10_relat_1(k2_funct_1('#skF_2'), k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_3403])).
% 12.73/5.75  tff(c_46, plain, (![B_37, A_36]: (k10_relat_1(k2_funct_1(B_37), A_36)=k9_relat_1(B_37, A_36) | ~v2_funct_1(B_37) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.73/5.75  tff(c_10056, plain, (![B_242, A_243, A_244]: (k2_xboole_0(k10_relat_1(k2_funct_1(B_242), A_243), k9_relat_1(B_242, A_244))=k10_relat_1(k2_funct_1(B_242), k2_xboole_0(A_243, A_244)) | ~v1_relat_1(k2_funct_1(B_242)) | ~v2_funct_1(B_242) | ~v1_funct_1(B_242) | ~v1_relat_1(B_242))), inference(superposition, [status(thm), theory('equality')], [c_46, c_753])).
% 12.73/5.75  tff(c_10083, plain, (![A_244]: (k10_relat_1(k2_funct_1('#skF_2'), k2_xboole_0(k1_xboole_0, A_244))=k2_xboole_0(k1_xboole_0, k9_relat_1('#skF_2', A_244)) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3419, c_10056])).
% 12.73/5.75  tff(c_10127, plain, (![A_244]: (k10_relat_1(k2_funct_1('#skF_2'), A_244)=k9_relat_1('#skF_2', A_244))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_3298, c_186, c_186, c_10083])).
% 12.73/5.75  tff(c_3420, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_3403])).
% 12.73/5.75  tff(c_775, plain, (![A_22, A_102]: (k2_xboole_0(k10_relat_1(A_22, A_102), k1_relat_1(A_22))=k10_relat_1(A_22, k2_xboole_0(A_102, k2_relat_1(A_22))) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_30, c_753])).
% 12.73/5.75  tff(c_3500, plain, (k10_relat_1(k2_funct_1('#skF_2'), k2_xboole_0(k1_xboole_0, k2_relat_1(k2_funct_1('#skF_2'))))=k2_xboole_0(k1_xboole_0, k1_relat_1(k2_funct_1('#skF_2'))) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3419, c_775])).
% 12.73/5.75  tff(c_3557, plain, (k10_relat_1(k2_funct_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))=k1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_3298, c_186, c_186, c_3500])).
% 12.73/5.75  tff(c_3766, plain, (k9_relat_1(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_3557, c_882])).
% 12.73/5.75  tff(c_3825, plain, (k9_relat_1(k2_funct_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_3420, c_3766])).
% 12.73/5.75  tff(c_48, plain, (![B_39, A_38]: (k9_relat_1(k2_funct_1(B_39), A_38)=k10_relat_1(B_39, A_38) | ~v2_funct_1(B_39) | ~v1_funct_1(B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_115])).
% 12.73/5.75  tff(c_4263, plain, (k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3825, c_48])).
% 12.73/5.75  tff(c_4286, plain, (k10_relat_1('#skF_2', k1_relat_1(k2_funct_1('#skF_2')))=k2_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_4263])).
% 12.73/5.75  tff(c_32, plain, (![B_24, A_23]: (r1_tarski(k10_relat_1(B_24, A_23), k10_relat_1(B_24, k2_relat_1(B_24))) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.73/5.75  tff(c_2888, plain, (![A_23]: (r1_tarski(k10_relat_1('#skF_2', A_23), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2831, c_32])).
% 12.73/5.75  tff(c_2932, plain, (![A_23]: (r1_tarski(k10_relat_1('#skF_2', A_23), k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2888])).
% 12.73/5.75  tff(c_4300, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4286, c_2932])).
% 12.73/5.75  tff(c_3297, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_3284])).
% 12.73/5.75  tff(c_627, plain, (![B_89]: (k9_relat_1(B_89, k2_relat_1(k2_funct_1(B_89)))=k1_relat_1(k2_funct_1(B_89)) | ~v2_funct_1(B_89) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89) | ~v1_relat_1(k2_funct_1(B_89)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_603])).
% 12.73/5.75  tff(c_50, plain, (![A_40, B_41, C_42]: (r1_tarski(A_40, B_41) | ~v2_funct_1(C_42) | ~r1_tarski(A_40, k1_relat_1(C_42)) | ~r1_tarski(k9_relat_1(C_42, A_40), k9_relat_1(C_42, B_41)) | ~v1_funct_1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_127])).
% 12.73/5.75  tff(c_2954, plain, (![B_41]: (r1_tarski(k1_relat_1('#skF_2'), B_41) | ~v2_funct_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1('#skF_2'), k9_relat_1('#skF_2', B_41)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2915, c_50])).
% 12.73/5.75  tff(c_4606, plain, (![B_178]: (r1_tarski(k1_relat_1('#skF_2'), B_178) | ~r1_tarski(k2_relat_1('#skF_2'), k9_relat_1('#skF_2', B_178)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_8, c_54, c_2954])).
% 12.73/5.75  tff(c_4610, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2'))) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_627, c_4606])).
% 12.73/5.75  tff(c_4637, plain, (r1_tarski(k1_relat_1('#skF_2'), k2_relat_1(k2_funct_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_60, c_58, c_54, c_3297, c_4610])).
% 12.73/5.75  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/5.75  tff(c_4653, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4637, c_4])).
% 12.73/5.75  tff(c_4662, plain, (k2_relat_1(k2_funct_1('#skF_2'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4300, c_4653])).
% 12.73/5.75  tff(c_44, plain, (![B_35, A_34]: (k9_relat_1(B_35, k10_relat_1(B_35, A_34))=A_34 | ~r1_tarski(A_34, k2_relat_1(B_35)) | ~v1_funct_1(B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.73/5.75  tff(c_4702, plain, (![A_34]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_34))=A_34 | ~r1_tarski(A_34, k1_relat_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4662, c_44])).
% 12.73/5.75  tff(c_4724, plain, (![A_34]: (k9_relat_1(k2_funct_1('#skF_2'), k10_relat_1(k2_funct_1('#skF_2'), A_34))=A_34 | ~r1_tarski(A_34, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3298, c_3420, c_4702])).
% 12.73/5.75  tff(c_26847, plain, (![A_405]: (k9_relat_1(k2_funct_1('#skF_2'), k9_relat_1('#skF_2', A_405))=A_405 | ~r1_tarski(A_405, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10127, c_4724])).
% 12.73/5.75  tff(c_26901, plain, (![A_405]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_405))=A_405 | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~r1_tarski(A_405, k1_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26847, c_48])).
% 12.73/5.75  tff(c_27357, plain, (![A_408]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_408))=A_408 | ~r1_tarski(A_408, k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_26901])).
% 12.73/5.75  tff(c_27388, plain, (k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(resolution, [status(thm)], [c_56, c_27357])).
% 12.73/5.75  tff(c_27416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_27388])).
% 12.73/5.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/5.75  
% 12.73/5.75  Inference rules
% 12.73/5.75  ----------------------
% 12.73/5.75  #Ref     : 0
% 12.73/5.75  #Sup     : 6422
% 12.73/5.75  #Fact    : 0
% 12.73/5.75  #Define  : 0
% 12.73/5.75  #Split   : 5
% 12.73/5.75  #Chain   : 0
% 12.73/5.75  #Close   : 0
% 12.73/5.75  
% 12.73/5.75  Ordering : KBO
% 12.73/5.75  
% 12.73/5.75  Simplification rules
% 12.73/5.75  ----------------------
% 12.73/5.75  #Subsume      : 333
% 12.73/5.75  #Demod        : 12717
% 12.73/5.75  #Tautology    : 3469
% 12.73/5.75  #SimpNegUnit  : 1
% 12.73/5.75  #BackRed      : 25
% 12.73/5.75  
% 12.73/5.75  #Partial instantiations: 0
% 12.73/5.75  #Strategies tried      : 1
% 12.73/5.75  
% 12.73/5.75  Timing (in seconds)
% 12.73/5.75  ----------------------
% 12.73/5.76  Preprocessing        : 0.37
% 12.73/5.76  Parsing              : 0.19
% 12.73/5.76  CNF conversion       : 0.02
% 12.73/5.76  Main loop            : 4.56
% 12.73/5.76  Inferencing          : 0.82
% 12.73/5.76  Reduction            : 2.83
% 12.73/5.76  Demodulation         : 2.54
% 12.73/5.76  BG Simplification    : 0.09
% 12.73/5.76  Subsumption          : 0.64
% 12.73/5.76  Abstraction          : 0.18
% 12.73/5.76  MUC search           : 0.00
% 12.73/5.76  Cooper               : 0.00
% 12.73/5.76  Total                : 4.97
% 12.73/5.76  Index Insertion      : 0.00
% 12.73/5.76  Index Deletion       : 0.00
% 12.73/5.76  Index Matching       : 0.00
% 12.73/5.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
