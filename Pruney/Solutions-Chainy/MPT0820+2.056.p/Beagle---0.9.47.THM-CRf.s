%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:08 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 573 expanded)
%              Number of leaves         :   30 ( 194 expanded)
%              Depth                    :   14
%              Number of atoms          :  214 (1081 expanded)
%              Number of equality atoms :   59 ( 205 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_82,axiom,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_12,c_49])).

tff(c_24,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_64,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_77,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70])).

tff(c_56,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_19,B_20)),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_23] :
      ( r1_tarski(A_23,k2_zfmisc_1(k1_relat_1(A_23),k2_relat_1(A_23)))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_445,plain,(
    ! [A_80,C_81,B_82,D_83] :
      ( r1_tarski(A_80,C_81)
      | k2_zfmisc_1(A_80,B_82) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_80,B_82),k2_zfmisc_1(C_81,D_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_449,plain,(
    ! [A_80,B_82] :
      ( r1_tarski(A_80,k1_relat_1(k2_zfmisc_1(A_80,B_82)))
      | k2_zfmisc_1(A_80,B_82) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_80,B_82)) ) ),
    inference(resolution,[status(thm)],[c_30,c_445])).

tff(c_459,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,k1_relat_1(k2_zfmisc_1(A_84,B_85)))
      | k2_zfmisc_1(A_84,B_85) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_449])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_461,plain,(
    ! [A_84,B_85] :
      ( k1_relat_1(k2_zfmisc_1(A_84,B_85)) = A_84
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(A_84,B_85)),A_84)
      | k2_zfmisc_1(A_84,B_85) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_459,c_2])).

tff(c_470,plain,(
    ! [A_84,B_85] :
      ( k1_relat_1(k2_zfmisc_1(A_84,B_85)) = A_84
      | k2_zfmisc_1(A_84,B_85) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_461])).

tff(c_28,plain,(
    ! [A_21,B_22] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_21,B_22)),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_372,plain,(
    ! [B_72,D_73,A_74,C_75] :
      ( r1_tarski(B_72,D_73)
      | k2_zfmisc_1(A_74,B_72) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_74,B_72),k2_zfmisc_1(C_75,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_376,plain,(
    ! [B_72,A_74] :
      ( r1_tarski(B_72,k2_relat_1(k2_zfmisc_1(A_74,B_72)))
      | k2_zfmisc_1(A_74,B_72) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_74,B_72)) ) ),
    inference(resolution,[status(thm)],[c_30,c_372])).

tff(c_387,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(B_76,k2_relat_1(k2_zfmisc_1(A_77,B_76)))
      | k2_zfmisc_1(A_77,B_76) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_376])).

tff(c_389,plain,(
    ! [A_77,B_76] :
      ( k2_relat_1(k2_zfmisc_1(A_77,B_76)) = B_76
      | ~ r1_tarski(k2_relat_1(k2_zfmisc_1(A_77,B_76)),B_76)
      | k2_zfmisc_1(A_77,B_76) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_387,c_2])).

tff(c_402,plain,(
    ! [A_78,B_79] :
      ( k2_relat_1(k2_zfmisc_1(A_78,B_79)) = B_79
      | k2_zfmisc_1(A_78,B_79) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_389])).

tff(c_22,plain,(
    ! [A_16] :
      ( k2_xboole_0(k1_relat_1(A_16),k2_relat_1(A_16)) = k3_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_415,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_78,B_79)),B_79) = k3_relat_1(k2_zfmisc_1(A_78,B_79))
      | ~ v1_relat_1(k2_zfmisc_1(A_78,B_79))
      | k2_zfmisc_1(A_78,B_79) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_22])).

tff(c_1215,plain,(
    ! [A_120,B_121] :
      ( k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_120,B_121)),B_121) = k3_relat_1(k2_zfmisc_1(A_120,B_121))
      | k2_zfmisc_1(A_120,B_121) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_415])).

tff(c_1367,plain,(
    ! [A_129,B_130] :
      ( k3_relat_1(k2_zfmisc_1(A_129,B_130)) = k2_xboole_0(A_129,B_130)
      | k2_zfmisc_1(A_129,B_130) = k1_xboole_0
      | k2_zfmisc_1(A_129,B_130) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_1215])).

tff(c_32,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k3_relat_1(A_24),k3_relat_1(B_26))
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1410,plain,(
    ! [A_24,A_129,B_130] :
      ( r1_tarski(k3_relat_1(A_24),k2_xboole_0(A_129,B_130))
      | ~ r1_tarski(A_24,k2_zfmisc_1(A_129,B_130))
      | ~ v1_relat_1(k2_zfmisc_1(A_129,B_130))
      | ~ v1_relat_1(A_24)
      | k2_zfmisc_1(A_129,B_130) = k1_xboole_0
      | k2_zfmisc_1(A_129,B_130) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1367,c_32])).

tff(c_1613,plain,(
    ! [A_141,A_142,B_143] :
      ( r1_tarski(k3_relat_1(A_141),k2_xboole_0(A_142,B_143))
      | ~ r1_tarski(A_141,k2_zfmisc_1(A_142,B_143))
      | ~ v1_relat_1(A_141)
      | k2_zfmisc_1(A_142,B_143) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1410])).

tff(c_36,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1625,plain,
    ( ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3')
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1613,c_36])).

tff(c_1665,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_56,c_1625])).

tff(c_78,plain,(
    ! [A_7] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_64])).

tff(c_79,plain,(
    ! [A_7] : ~ v1_relat_1(A_7) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_77])).

tff(c_103,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_34,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_274,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k3_relat_1(A_67),k3_relat_1(B_68))
      | ~ r1_tarski(A_67,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_291,plain,(
    ! [A_67] :
      ( r1_tarski(k3_relat_1(A_67),k1_xboole_0)
      | ~ r1_tarski(A_67,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_274])).

tff(c_302,plain,(
    ! [A_69] :
      ( r1_tarski(k3_relat_1(A_69),k1_xboole_0)
      | ~ r1_tarski(A_69,k1_xboole_0)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_291])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_64])).

tff(c_310,plain,(
    ! [A_69] :
      ( v1_relat_1(k3_relat_1(A_69))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(A_69,k1_xboole_0)
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_302,c_74])).

tff(c_323,plain,(
    ! [A_69] :
      ( v1_relat_1(k3_relat_1(A_69))
      | ~ r1_tarski(A_69,k1_xboole_0)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_310])).

tff(c_762,plain,(
    ! [A_102,B_103] :
      ( v1_relat_1(k3_relat_1(A_102))
      | ~ v1_relat_1(k3_relat_1(B_103))
      | ~ r1_tarski(A_102,B_103)
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_274,c_74])).

tff(c_863,plain,(
    ! [A_106,A_107] :
      ( v1_relat_1(k3_relat_1(A_106))
      | ~ r1_tarski(A_106,A_107)
      | ~ v1_relat_1(A_106)
      | ~ r1_tarski(A_107,k1_xboole_0)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_323,c_762])).

tff(c_881,plain,
    ( v1_relat_1(k3_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k1_xboole_0)
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_863])).

tff(c_908,plain,
    ( v1_relat_1(k3_relat_1('#skF_3'))
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_77,c_881])).

tff(c_912,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_908])).

tff(c_1677,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1665,c_912])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1677])).

tff(c_1686,plain,(
    r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_908])).

tff(c_128,plain,(
    ! [B_46,A_47] :
      ( B_46 = A_47
      | ~ r1_tarski(B_46,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_57,c_128])).

tff(c_1772,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1686,c_139])).

tff(c_140,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_128])).

tff(c_243,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_1781,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1772,c_243])).

tff(c_1787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1781])).

tff(c_1788,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1805,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_26])).

tff(c_1828,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1805,c_2])).

tff(c_2324,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1828])).

tff(c_2387,plain,(
    ! [A_198,C_199,B_200,D_201] :
      ( r1_tarski(A_198,C_199)
      | k2_zfmisc_1(A_198,B_200) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_198,B_200),k2_zfmisc_1(C_199,D_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2397,plain,(
    ! [A_198,B_200] :
      ( r1_tarski(A_198,k1_relat_1(k2_zfmisc_1(A_198,B_200)))
      | k2_zfmisc_1(A_198,B_200) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_198,B_200)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2387])).

tff(c_2408,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(A_202,k1_relat_1(k2_zfmisc_1(A_202,B_203)))
      | k2_zfmisc_1(A_202,B_203) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2397])).

tff(c_2416,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_2408])).

tff(c_2424,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_2416])).

tff(c_2425,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2324,c_2424])).

tff(c_2437,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_57])).

tff(c_2439,plain,(
    k3_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2425,c_2425,c_34])).

tff(c_2463,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2439,c_36])).

tff(c_2466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2463])).

tff(c_2467,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1828])).

tff(c_1802,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_28])).

tff(c_1835,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1802,c_2])).

tff(c_1852,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1835])).

tff(c_2190,plain,(
    ! [B_181,D_182,A_183,C_184] :
      ( r1_tarski(B_181,D_182)
      | k2_zfmisc_1(A_183,B_181) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_183,B_181),k2_zfmisc_1(C_184,D_182)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2200,plain,(
    ! [B_181,A_183] :
      ( r1_tarski(B_181,k2_relat_1(k2_zfmisc_1(A_183,B_181)))
      | k2_zfmisc_1(A_183,B_181) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_183,B_181)) ) ),
    inference(resolution,[status(thm)],[c_30,c_2190])).

tff(c_2211,plain,(
    ! [B_185,A_186] :
      ( r1_tarski(B_185,k2_relat_1(k2_zfmisc_1(A_186,B_185)))
      | k2_zfmisc_1(A_186,B_185) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2200])).

tff(c_2219,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_2211])).

tff(c_2227,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1788,c_2219])).

tff(c_2228,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1852,c_2227])).

tff(c_2244,plain,(
    ! [A_7] : r1_tarski('#skF_3',A_7) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_57])).

tff(c_2246,plain,(
    k3_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_2228,c_34])).

tff(c_2270,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_36])).

tff(c_2273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_2270])).

tff(c_2274,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1835])).

tff(c_2281,plain,
    ( k2_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k3_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2274,c_22])).

tff(c_2288,plain,(
    k2_xboole_0(k1_relat_1('#skF_3'),'#skF_2') = k3_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2281])).

tff(c_2470,plain,(
    k2_xboole_0('#skF_1','#skF_2') = k3_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2467,c_2288])).

tff(c_2489,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k3_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2470,c_36])).

tff(c_2492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 12:26:07 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.95/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.72  
% 3.95/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.72  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.95/1.72  
% 3.95/1.72  %Foreground sorts:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Background operators:
% 3.95/1.72  
% 3.95/1.72  
% 3.95/1.72  %Foreground operators:
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.95/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.95/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.95/1.72  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.95/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.95/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.95/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.95/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.95/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.95/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.95/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.95/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.95/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.95/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.95/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.95/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.95/1.72  
% 3.95/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.95/1.75  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.95/1.75  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.95/1.75  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.95/1.75  tff(f_87, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 3.95/1.75  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.95/1.75  tff(f_66, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 3.95/1.75  tff(f_72, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.95/1.75  tff(f_39, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.95/1.75  tff(f_68, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 3.95/1.75  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.95/1.75  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 3.95/1.75  tff(f_82, axiom, (k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 3.95/1.75  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.75  tff(c_12, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.95/1.75  tff(c_49, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.75  tff(c_57, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_12, c_49])).
% 3.95/1.75  tff(c_24, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.95/1.75  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.95/1.75  tff(c_64, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.95/1.75  tff(c_70, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_64])).
% 3.95/1.75  tff(c_77, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_70])).
% 3.95/1.75  tff(c_56, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_49])).
% 3.95/1.75  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_19, B_20)), A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.95/1.75  tff(c_30, plain, (![A_23]: (r1_tarski(A_23, k2_zfmisc_1(k1_relat_1(A_23), k2_relat_1(A_23))) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.95/1.75  tff(c_445, plain, (![A_80, C_81, B_82, D_83]: (r1_tarski(A_80, C_81) | k2_zfmisc_1(A_80, B_82)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_80, B_82), k2_zfmisc_1(C_81, D_83)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.75  tff(c_449, plain, (![A_80, B_82]: (r1_tarski(A_80, k1_relat_1(k2_zfmisc_1(A_80, B_82))) | k2_zfmisc_1(A_80, B_82)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_80, B_82)))), inference(resolution, [status(thm)], [c_30, c_445])).
% 3.95/1.75  tff(c_459, plain, (![A_84, B_85]: (r1_tarski(A_84, k1_relat_1(k2_zfmisc_1(A_84, B_85))) | k2_zfmisc_1(A_84, B_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_449])).
% 3.95/1.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.75  tff(c_461, plain, (![A_84, B_85]: (k1_relat_1(k2_zfmisc_1(A_84, B_85))=A_84 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(A_84, B_85)), A_84) | k2_zfmisc_1(A_84, B_85)=k1_xboole_0)), inference(resolution, [status(thm)], [c_459, c_2])).
% 3.95/1.75  tff(c_470, plain, (![A_84, B_85]: (k1_relat_1(k2_zfmisc_1(A_84, B_85))=A_84 | k2_zfmisc_1(A_84, B_85)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_461])).
% 3.95/1.75  tff(c_28, plain, (![A_21, B_22]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_21, B_22)), B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.95/1.75  tff(c_372, plain, (![B_72, D_73, A_74, C_75]: (r1_tarski(B_72, D_73) | k2_zfmisc_1(A_74, B_72)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_74, B_72), k2_zfmisc_1(C_75, D_73)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.75  tff(c_376, plain, (![B_72, A_74]: (r1_tarski(B_72, k2_relat_1(k2_zfmisc_1(A_74, B_72))) | k2_zfmisc_1(A_74, B_72)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_74, B_72)))), inference(resolution, [status(thm)], [c_30, c_372])).
% 3.95/1.75  tff(c_387, plain, (![B_76, A_77]: (r1_tarski(B_76, k2_relat_1(k2_zfmisc_1(A_77, B_76))) | k2_zfmisc_1(A_77, B_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_376])).
% 3.95/1.75  tff(c_389, plain, (![A_77, B_76]: (k2_relat_1(k2_zfmisc_1(A_77, B_76))=B_76 | ~r1_tarski(k2_relat_1(k2_zfmisc_1(A_77, B_76)), B_76) | k2_zfmisc_1(A_77, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_387, c_2])).
% 3.95/1.75  tff(c_402, plain, (![A_78, B_79]: (k2_relat_1(k2_zfmisc_1(A_78, B_79))=B_79 | k2_zfmisc_1(A_78, B_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_389])).
% 3.95/1.75  tff(c_22, plain, (![A_16]: (k2_xboole_0(k1_relat_1(A_16), k2_relat_1(A_16))=k3_relat_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.95/1.75  tff(c_415, plain, (![A_78, B_79]: (k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_78, B_79)), B_79)=k3_relat_1(k2_zfmisc_1(A_78, B_79)) | ~v1_relat_1(k2_zfmisc_1(A_78, B_79)) | k2_zfmisc_1(A_78, B_79)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_402, c_22])).
% 3.95/1.75  tff(c_1215, plain, (![A_120, B_121]: (k2_xboole_0(k1_relat_1(k2_zfmisc_1(A_120, B_121)), B_121)=k3_relat_1(k2_zfmisc_1(A_120, B_121)) | k2_zfmisc_1(A_120, B_121)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_415])).
% 3.95/1.75  tff(c_1367, plain, (![A_129, B_130]: (k3_relat_1(k2_zfmisc_1(A_129, B_130))=k2_xboole_0(A_129, B_130) | k2_zfmisc_1(A_129, B_130)=k1_xboole_0 | k2_zfmisc_1(A_129, B_130)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_470, c_1215])).
% 3.95/1.75  tff(c_32, plain, (![A_24, B_26]: (r1_tarski(k3_relat_1(A_24), k3_relat_1(B_26)) | ~r1_tarski(A_24, B_26) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.95/1.75  tff(c_1410, plain, (![A_24, A_129, B_130]: (r1_tarski(k3_relat_1(A_24), k2_xboole_0(A_129, B_130)) | ~r1_tarski(A_24, k2_zfmisc_1(A_129, B_130)) | ~v1_relat_1(k2_zfmisc_1(A_129, B_130)) | ~v1_relat_1(A_24) | k2_zfmisc_1(A_129, B_130)=k1_xboole_0 | k2_zfmisc_1(A_129, B_130)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1367, c_32])).
% 3.95/1.75  tff(c_1613, plain, (![A_141, A_142, B_143]: (r1_tarski(k3_relat_1(A_141), k2_xboole_0(A_142, B_143)) | ~r1_tarski(A_141, k2_zfmisc_1(A_142, B_143)) | ~v1_relat_1(A_141) | k2_zfmisc_1(A_142, B_143)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1410])).
% 3.95/1.75  tff(c_36, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.95/1.75  tff(c_1625, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3') | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1613, c_36])).
% 3.95/1.75  tff(c_1665, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_77, c_56, c_1625])).
% 3.95/1.75  tff(c_78, plain, (![A_7]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_12, c_64])).
% 3.95/1.75  tff(c_79, plain, (![A_7]: (~v1_relat_1(A_7))), inference(splitLeft, [status(thm)], [c_78])).
% 3.95/1.75  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_77])).
% 3.95/1.75  tff(c_103, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_78])).
% 3.95/1.75  tff(c_34, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.95/1.75  tff(c_274, plain, (![A_67, B_68]: (r1_tarski(k3_relat_1(A_67), k3_relat_1(B_68)) | ~r1_tarski(A_67, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.95/1.75  tff(c_291, plain, (![A_67]: (r1_tarski(k3_relat_1(A_67), k1_xboole_0) | ~r1_tarski(A_67, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_34, c_274])).
% 3.95/1.75  tff(c_302, plain, (![A_69]: (r1_tarski(k3_relat_1(A_69), k1_xboole_0) | ~r1_tarski(A_69, k1_xboole_0) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_291])).
% 3.95/1.75  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.95/1.75  tff(c_74, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_16, c_64])).
% 3.95/1.75  tff(c_310, plain, (![A_69]: (v1_relat_1(k3_relat_1(A_69)) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(A_69, k1_xboole_0) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_302, c_74])).
% 3.95/1.75  tff(c_323, plain, (![A_69]: (v1_relat_1(k3_relat_1(A_69)) | ~r1_tarski(A_69, k1_xboole_0) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_310])).
% 3.95/1.75  tff(c_762, plain, (![A_102, B_103]: (v1_relat_1(k3_relat_1(A_102)) | ~v1_relat_1(k3_relat_1(B_103)) | ~r1_tarski(A_102, B_103) | ~v1_relat_1(B_103) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_274, c_74])).
% 3.95/1.75  tff(c_863, plain, (![A_106, A_107]: (v1_relat_1(k3_relat_1(A_106)) | ~r1_tarski(A_106, A_107) | ~v1_relat_1(A_106) | ~r1_tarski(A_107, k1_xboole_0) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_323, c_762])).
% 3.95/1.75  tff(c_881, plain, (v1_relat_1(k3_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_863])).
% 3.95/1.75  tff(c_908, plain, (v1_relat_1(k3_relat_1('#skF_3')) | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_77, c_881])).
% 3.95/1.75  tff(c_912, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_908])).
% 3.95/1.75  tff(c_1677, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1665, c_912])).
% 3.95/1.75  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_1677])).
% 3.95/1.75  tff(c_1686, plain, (r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_908])).
% 3.95/1.75  tff(c_128, plain, (![B_46, A_47]: (B_46=A_47 | ~r1_tarski(B_46, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.75  tff(c_139, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(resolution, [status(thm)], [c_57, c_128])).
% 3.95/1.75  tff(c_1772, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1686, c_139])).
% 3.95/1.75  tff(c_140, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_56, c_128])).
% 3.95/1.75  tff(c_243, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_140])).
% 3.95/1.75  tff(c_1781, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1772, c_243])).
% 3.95/1.75  tff(c_1787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_1781])).
% 3.95/1.75  tff(c_1788, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_140])).
% 3.95/1.75  tff(c_1805, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1788, c_26])).
% 3.95/1.75  tff(c_1828, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1805, c_2])).
% 3.95/1.75  tff(c_2324, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1828])).
% 3.95/1.75  tff(c_2387, plain, (![A_198, C_199, B_200, D_201]: (r1_tarski(A_198, C_199) | k2_zfmisc_1(A_198, B_200)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_198, B_200), k2_zfmisc_1(C_199, D_201)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.75  tff(c_2397, plain, (![A_198, B_200]: (r1_tarski(A_198, k1_relat_1(k2_zfmisc_1(A_198, B_200))) | k2_zfmisc_1(A_198, B_200)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_198, B_200)))), inference(resolution, [status(thm)], [c_30, c_2387])).
% 3.95/1.75  tff(c_2408, plain, (![A_202, B_203]: (r1_tarski(A_202, k1_relat_1(k2_zfmisc_1(A_202, B_203))) | k2_zfmisc_1(A_202, B_203)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2397])).
% 3.95/1.75  tff(c_2416, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1788, c_2408])).
% 3.95/1.75  tff(c_2424, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_2416])).
% 3.95/1.75  tff(c_2425, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2324, c_2424])).
% 3.95/1.75  tff(c_2437, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_57])).
% 3.95/1.75  tff(c_2439, plain, (k3_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2425, c_2425, c_34])).
% 3.95/1.75  tff(c_2463, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2439, c_36])).
% 3.95/1.75  tff(c_2466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2463])).
% 3.95/1.75  tff(c_2467, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1828])).
% 3.95/1.75  tff(c_1802, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1788, c_28])).
% 3.95/1.75  tff(c_1835, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1802, c_2])).
% 3.95/1.75  tff(c_1852, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1835])).
% 3.95/1.75  tff(c_2190, plain, (![B_181, D_182, A_183, C_184]: (r1_tarski(B_181, D_182) | k2_zfmisc_1(A_183, B_181)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_183, B_181), k2_zfmisc_1(C_184, D_182)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.75  tff(c_2200, plain, (![B_181, A_183]: (r1_tarski(B_181, k2_relat_1(k2_zfmisc_1(A_183, B_181))) | k2_zfmisc_1(A_183, B_181)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_183, B_181)))), inference(resolution, [status(thm)], [c_30, c_2190])).
% 3.95/1.75  tff(c_2211, plain, (![B_185, A_186]: (r1_tarski(B_185, k2_relat_1(k2_zfmisc_1(A_186, B_185))) | k2_zfmisc_1(A_186, B_185)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2200])).
% 3.95/1.75  tff(c_2219, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1788, c_2211])).
% 3.95/1.75  tff(c_2227, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1788, c_2219])).
% 3.95/1.75  tff(c_2228, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1852, c_2227])).
% 3.95/1.75  tff(c_2244, plain, (![A_7]: (r1_tarski('#skF_3', A_7))), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_57])).
% 3.95/1.75  tff(c_2246, plain, (k3_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_2228, c_34])).
% 3.95/1.75  tff(c_2270, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_36])).
% 3.95/1.75  tff(c_2273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2244, c_2270])).
% 3.95/1.75  tff(c_2274, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_1835])).
% 3.95/1.75  tff(c_2281, plain, (k2_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k3_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2274, c_22])).
% 3.95/1.75  tff(c_2288, plain, (k2_xboole_0(k1_relat_1('#skF_3'), '#skF_2')=k3_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2281])).
% 3.95/1.75  tff(c_2470, plain, (k2_xboole_0('#skF_1', '#skF_2')=k3_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2467, c_2288])).
% 3.95/1.75  tff(c_2489, plain, (~r1_tarski(k3_relat_1('#skF_3'), k3_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2470, c_36])).
% 3.95/1.75  tff(c_2492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2489])).
% 3.95/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.75  
% 3.95/1.75  Inference rules
% 3.95/1.75  ----------------------
% 3.95/1.75  #Ref     : 0
% 3.95/1.75  #Sup     : 502
% 3.95/1.75  #Fact    : 0
% 3.95/1.75  #Define  : 0
% 3.95/1.75  #Split   : 13
% 3.95/1.75  #Chain   : 0
% 3.95/1.75  #Close   : 0
% 3.95/1.75  
% 3.95/1.75  Ordering : KBO
% 3.95/1.75  
% 3.95/1.75  Simplification rules
% 3.95/1.75  ----------------------
% 3.95/1.75  #Subsume      : 80
% 3.95/1.75  #Demod        : 582
% 3.95/1.75  #Tautology    : 215
% 3.95/1.75  #SimpNegUnit  : 7
% 3.95/1.75  #BackRed      : 68
% 3.95/1.75  
% 3.95/1.75  #Partial instantiations: 0
% 3.95/1.75  #Strategies tried      : 1
% 3.95/1.75  
% 3.95/1.75  Timing (in seconds)
% 3.95/1.75  ----------------------
% 3.95/1.75  Preprocessing        : 0.30
% 3.95/1.75  Parsing              : 0.18
% 3.95/1.75  CNF conversion       : 0.02
% 3.95/1.75  Main loop            : 0.63
% 3.95/1.75  Inferencing          : 0.22
% 3.95/1.75  Reduction            : 0.22
% 3.95/1.75  Demodulation         : 0.16
% 3.95/1.75  BG Simplification    : 0.02
% 3.95/1.75  Subsumption          : 0.13
% 3.95/1.75  Abstraction          : 0.03
% 3.95/1.75  MUC search           : 0.00
% 3.95/1.75  Cooper               : 0.00
% 3.95/1.75  Total                : 0.99
% 3.95/1.75  Index Insertion      : 0.00
% 3.95/1.75  Index Deletion       : 0.00
% 3.95/1.75  Index Matching       : 0.00
% 3.95/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
